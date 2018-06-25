// Seastar "external sort" code, Will Wray April 2017

#include "core/app-template.hh"
#include "core/bitops.hh"
#include "core/file.hh"
#include "core/fstream.hh"
#include "core/gate.hh"
#include "core/iostream.hh"
#include "core/reactor.hh"
#include "core/semaphore.hh"
#include "core/shared_future.hh"
#include "core/sleep.hh"

#include "core/fsqual.hh"

#include <sys/uio.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iterator>
#include <numeric>
#include <random>
#include <utility>

using namespace std::chrono_literals;

//template <typename T, size_t N>
//constexpr size_t size(T (&a)[N]) { return N; }

template <typename T>
concept bool Integral = std::is_integral<T>::value;

template <typename T>
concept bool UnsignedIntegral = Integral<T> && std::is_unsigned<T>::value;

// uint_holds_t<N,T,F> conditionally returns T if it can hold N else F
template <uintmax_t N, UnsignedIntegral T, UnsignedIntegral F>
using uint_holds_t = std::conditional_t< T(N)==N, T, F>;

// uint_least_t<N> is the smallest unsigned integer type that holds value N
template <uintmax_t N>
using uint_least_t = uint_holds_t<N, unsigned char,
                     uint_holds_t<N, unsigned short,
                     uint_holds_t<N, unsigned int,
                     uint_holds_t<N, unsigned long,
                                     unsigned long long>>>>;
// test uint_least_t<N>
using std::is_same;
static_assert( is_same< uint_least8_t,  uint_least_t<0>>{});
static_assert( is_same< uint_least8_t,  uint_least_t<1>>{});
static_assert( is_same< uint_least8_t,  uint_least_t<0x0ff>>{});
static_assert( is_same< uint_least16_t, uint_least_t<0x100>>{});
static_assert( is_same< uint_least16_t, uint_least_t<0x0ffff>>{});
static_assert( is_same< uint_least32_t, uint_least_t<0x10000>>{});
static_assert( is_same< uint_least32_t, uint_least_t<0x0ffffffff>>{});
static_assert( is_same< uint_least64_t, uint_least_t<0x100000000>>{});
static_assert( is_same< uint_least64_t, uint_least_t<uint64_t(-1)>>{});
static_assert( is_same< uintmax_t,      uint_least_t<uintmax_t(-1)>>{});

// make an array from an integer_sequence template-parameter-pack
// i.e. constexpr, compile-time, static initialisation
// e.g. auto iota32 = make_array(std::make_index_sequence<32>())
template <Integral I, size_t... Is>
constexpr std::array<I,sizeof...(Is)> make_array(std::integer_sequence<I,Is...>)
{ return {Is...}; }

// iota convenience function for initialisation with std::iota
// e.g. auto a = iota<std::array<unsigned,4096>>();
//      auto v = iota(std::vector<unsigned>(32768));
template <typename Seq>
Seq iota( Seq v={}) { std::iota(v.begin(),v.end(),0); return v; }

// as_array<N>(Tptr)->array<T,N>&  poor-man's array_view / span
// Casts a pointer to a static-sized array reference of the same value type
// (unfortunately, the reinterpret_cast disallows constexpr)
template <size_t N, typename T>
std::array<T,N>& as_array(T* p)
{ return *reinterpret_cast<std::array<T,N>*>(p); }

using byte = uint8_t;
// bytes is a byte array alias
template <unsigned n_bytes>
using bytes = std::array< byte, n_bytes>;

// bitref type for implementation of bit twiddling.
// Encapsulates a reference to a word and a bitmask.
// Implicit conversion to bool = word & mask
// (true if any mask bit of the word is set)
template <UnsignedIntegral U>
struct bitref
{
  U& word;
  U  mask;
  constexpr operator bool() const { return any(); }
  constexpr bool any() const { return word & mask; }
  constexpr bool all() const { return (word&mask)==mask; }
  // Member fns set,clear,toggle,= mutate the referenced word
  constexpr void set() const { word |= mask; }
  constexpr void clear() const { word &= ~mask; }
  constexpr void toggle() const  { word ^= mask; }
  constexpr bitref operator=(bool b) const
  {
    if (b) set(); else clear();
    return *this;
  }
};

template <UnsignedIntegral U>
constexpr bool test_bitref()
{
  bool res{true};
  U u{};
  for (U bit=1; bit; bit<<=1)
  {
    bitref<U>
    br{u,bit};   res = res && !br && u==0 && !br.any() && !br.all();
    br.set();    res = res && br  && u==bit && br.any() && br.all();
    br.clear();  res = res && !br && u==0;
    br.toggle(); res = res && br  && u==bit;
    br.toggle(); res = res && !br && u==0;
    br = true;   res = res && br  && u==bit;
    br = false;  res = res && !br && u==0;
  }
  return res;
}
static_assert(test_bitref<uint8_t>(),"");
static_assert(test_bitref<uint16_t>(),"");
static_assert(test_bitref<uint32_t>(),"");
static_assert(test_bitref<uint64_t>(),"");

// Bit indexing of big-endian bitstring-array with index 0 the most sig bit
// e.g. bit(bytes,i) returns a bitref for twiddling bit i of byte array bytes.
template <typename A, typename U=typename A::value_type>
requires UnsignedIntegral<U>
constexpr auto bit(A const& a, unsigned i)
{
  constexpr unsigned bits = std::numeric_limits<U>::digits;
  constexpr U msb = std::numeric_limits<std::make_signed_t<U>>::min();
  return bitref<U>{ const_cast<U&>(a[i/bits]), static_cast<U>(msb >> (i%bits)) };
}

constexpr bool test_bit()
{
  // array of 64 bits with each 9th bit set
  //                       0    9    18   27   36   45   54   63
  std::array<byte,8> msb{0x80,0x40,0x20,0x10,0x08,0x04,0x02,0x01};
  bool res{true};
  for (unsigned i=0; i<8*msb.size(); ++i)
  {
    res = res && bit(msb,i)!=bool(i%9);
  }
  return res;
}
static_assert(test_bit(),"");

/*================================================================
  File record size and partition size constants
   D = data size; number of records in the input file
   P = partition size; number of records in a partition
   K = (D+P-1)/P; number of partitions in the file
   PK = D - (K-1)*P; size of the final, Kth, partition
*/

// 4K byte record size, 2^12 bytes
constexpr int fourK {4096};

// P = partition size in records
//   = 2^16 = 64K records in order to fit uint16_t for tight indexing
constexpr size_t P = 1<<16;

// sizeof file partition in bytes.
// For 2^16 4K records, the file partition size is 2^28 = 256M
constexpr size_t partition_size = P*fourK;

// rec4k, four kilobyte data record
// 4Kbyte fixed length record, 4096 = 4x1024 = 2^12 bytes,
//         = 2^15 = 32768 bits, 64x64-byte cachelines,...
//         8 fit in 32K L1 data cache, 64 in 256K L2 cache.
// Good for disk 4K sector size alignment and DMA, but...
// want to avoid 4K-aliasing cache collisions on coherent
// strided accesses to a contiguous sequence of 4K records.
// -> Deliberately mis-align the data when read into RAM?
using rec4K = bytes<fourK>;
// std array comparison is lexicographic, hopefully optimized.

// Generator interface
//   A generator is a function object with member functions:
//     operator() -> T, returns successive values of type T
//     count()-> size_t returns the number of T's generated so far
//     size() -> size_t returns the total number of T's that can be generated

// end_exception is thrown when a generator is called after it is ended
struct end_exception : std::exception {};

// rec4K counting-generator options
enum class Reverse {no,yes};
enum class Explode {no,yes};
enum class Justify {left,center,right};

// Counting generator
// Generates N Recs with bits of the count {0,1,...,N-2,N-1}.
// Optionally, reverse the count, 'explode' the count's bits
// so they are maximally separated through the 32768 rec4K bits,
// with bits packed to the left (MSB), right (LSB) or center.
//
// () function call operator is the generator function
// size()  returns N, the total length of the generator sequence
// count() returns the index of the last generated 
template <typename Rec,
          size_t N,
          Reverse rev   = Reverse::no,
          Explode xplod = Explode::no,
          Justify just  = Justify::right>
class CountingGenerator
{
  // Define some constants, using enum for convenience 
  enum : unsigned {
          N_bmax = 32,                    // max number of bits for N Nmax=2^32
          N_bits = log2ceil(N),
          center = just==Justify::center,
          right  = just==Justify::right,
          nxplod = xplod==Explode::no,
          spaces = (nxplod ? 1 : N_bits) + center,
          bspace =  nxplod ? 1 : fourK*8*N_bmax/spaces,
          offset = right ? 0 
                          : nxplod ? (fourK*8-N_bits+center)/spaces
                                  : bspace-1
  };
  static_assert(N && N_bits<=N_bmax);

  size_t _count{0};

 public:
  using value_type=Rec;
  static constexpr size_t size() { return N; }
  size_t count() const { return _count; }

  // Generate a record with bits of the count.
  inline Rec operator()()
  {
    if (_count==N) throw end_exception{};

    auto n = (rev==Reverse::no ? _count++ : N - ++_count);

    Rec rec{};
    for (unsigned bitmask=1<<N_bits, index=offset;
         bitmask;
         bitmask=bitmask>>1,         index+=bspace)
    {
      if (n&bitmask)
        bit(rec, nxplod ? index : index/N_bmax).set();
    }
    return rec;
  }
};



// iov_buffers <Rec, n_4K=1> (n_buf=1, n_iov=32)
//   Buffers for iovec vectored IO: array<Buffer,n_buf>
//   A single, fixed-length, aligned allocation of Rec elements.
//   For use with Seastar's read_dma/write_dma file functions
//   taking a vector<iovec> arg (and calling POSIX readv/writev).
//   Also keeps track of file pos for convenience in sequential io.
//
// Each n_buf buffer can be filled with up to capacity() Rec records
//                           capacity = n_iovs x rec_per_iov records
// Each buffer is divided into n_iov iov subarrays (4K multiple size)
//                            iovsize = n_4K x fourK
// capacity() Returns the fixed maximum number of Recs per buffer.
// fill(b,gen) Trys to fill buffer b to capacity with generator gen.
//         Returns the num filled. Keeps track of file pos.
// size()  Returns the num filled by previous fill().
//         Condition (size < capacity) indicates that fill is done.
// bget(b) Returns a pointer to buffer b (char*)
// iov(b)  Returns a vector of iovec offset pointers into buffer b.
// pos()   Returns the file position as tracked by fill()
//
//    Rec: record type
//   n_4K: how many multiples of 4K in each iov
//  n_buf: number of buffers
//  n_iov: number of iovs per buffer
//
constexpr unsigned num_4Ks_per_iov{1};
constexpr unsigned num_iov_per_buf{32};

template <typename Rec,
          unsigned n_4K = num_4Ks_per_iov,
          unsigned n_iov = num_iov_per_buf>
using iov_buffer = std::enable_if_t<fourK*n_4K % sizeof(Rec)==0,
                   std::array< Rec, fourK*n_4K*n_iov/sizeof(Rec)>>;

// Returns a vector of iovec entries with offsets to the buffer's iovs
template <unsigned n_iov = num_iov_per_buf, typename Rec, size_t N>
std::vector<iovec> iov(std::array<Rec,N>& iovbuf, size_t nrecs=N)
{
  constexpr unsigned rec_per_iov = N/n_iov;
  size_t niovs = (nrecs+rec_per_iov-1)/rec_per_iov;
  std::vector<iovec> viov(niovs);
  for (size_t i=0; i<niovs; ++i)
  {
    viov[i].iov_base = reinterpret_cast<char*>(&iovbuf[i*rec_per_iov]);
    viov[i].iov_len = sizeof(iovbuf)/n_iov;
  }
  if (nrecs%rec_per_iov)
  {
    viov.back().iov_len = nrecs%rec_per_iov;      
  }
  return viov;
}

template <typename Rec,
          unsigned n_4K =  num_4Ks_per_iov,
          unsigned n_iov = num_iov_per_buf>
class iov_buffers
{
  using buffer = iov_buffer<Rec,n_4K,n_iov>;
  // return type of allocate_aligned_buffer<char>(size_t,size_t)
  using uniq_buf = std::unique_ptr<char[], free_deleter>;
  
  uniq_buf buf;
  size_t n_buffers=1;

 public:
  iov_buffers(size_t n_buf=1)
    : buf{ allocate_aligned_buffer<char>(n_buf*n_iov*n_4K*fourK, 4096)}
    , n_buffers{n_buf}
  {
    new (buf.get()) buffer[n_buffers];
  }

  ~iov_buffers() { delete[] buf.get(); }

  iov_buffers(iov_buffers&&)=default;

  buffer& operator[](size_t b) const {
    return *(reinterpret_cast<buffer*>(buf.get()) + b);
  }

  buffer* begin() { return &(*this)[0]; }
  buffer* end() { return &(*this)[n_buffers]; }
};

struct pos_len { size_t pos; size_t len; };

template <typename Buf, typename Gen>
pos_len fill(Buf& buf, Gen& gen)
{
  using Rec=typename Gen::value_type;
  pos_len ret {gen.count()*sizeof(Rec),
               std::min(size(buf), gen.size()-gen.count())};
  std::generate_n( buf.begin(), ret.len, std::ref(gen));
  // for (auto rec=buf.begin(); rec!=buf.begin()+ret.len; ++rec)
  // {
  //   *rec=gen();
  // }
  return ret;
}

#if 0
  // Trys to fill capacity() records of buffer b from gen / file.
  // Returns (for Gen=gen) size; the number of records filled.
  // Returns (for Gen=file) future<size>, pending iov read completion
  // After a fill is done,  size() < capacity() indicates end
  template <typename Gen>
  auto fill(size_t b, Gen& gen) { return filler(b,gen); }

  // Returns a vector of iovec entries with offsets into buf
  std::vector<iovec> iov(size_t b, size_t nrecs=capacity())
  {
    size_t iovs = (nrecs+rec_per_iov-1)/rec_per_iov;
    std::vector<iovec> viov(iovs);
    for (size_t i=0; i<iovs; ++i)
    {
      viov[i].iov_base = bget(b)+i*iovsize;
      viov[i].iov_len = iovsize;
    }
    if (nrecs%rec_per_iov)
    {
      viov.back().iov_len = nrecs%rec_per_iov;      
    }
    return viov;
  }
  // iovec with size equal to the previous fill() (for writing)
  std::vector<iovec> iov_w(size_t b) { return iov(b,size()); }

  Rec* begin(size_t b) { return reinterpret_cast<Rec*>(bget(b)); }
  Rec* end(size_t b) const { return reinterpret_cast<Rec*>(bget(b))+size(); }

 private:
  template <typename Gen>
  size_t filler(size_t i, Gen& gen)
  {
    _pos = gen.count()*sizeof(Rec);
    _size = std::min(capacity(), gen.size()-gen.count());
    std::generate( begin(i), begin(i)+_size, gen);
    //for (auto rec=begin(); rec!=end(); ++rec) *rec = gen();
    return size();
  }

  // filler taking a file to read from, keeping track of pos
  future<size_t> filler(size_t i, file& f)
  {
    return f.dma_read(_pos,iov(i)).then([this] (size_t r)
    {
      assert(r%sizeof(Rec)==0);
      _pos += r;
      _size = r/sizeof(Rec);
      return r/sizeof(Rec);
    });
  }

};

class writer
{
  file& f;
  size_t pos=0;
  unsigned fill_size=0;

 public:
  writer(file& f) : f{f}, pos{0} {}

  template <typename Gen, typename Buf>
  unsigned fill(Buf& buf, Gen& gen)
  {
    pos = gen.count()*sizeof(Gen::value_type);
    fill_size = std::min(std::size(buf), gen.size()-gen.count());
    std::generate( begin(i), begin(i)+fill_size, gen);
    //for (auto rec=begin(); rec!=end(); ++rec) *rec = gen();
    return fill_size;
  }

  template <typename Gen, typename Buf>
  unsigned fillbuf(Buf& buf)

  template <typename Gen, typename Buf>
  future<size_t> writebuf(Buf const& buf)
  {
    return f.dma_write(pos, buf.iov(buf_size)).then([&pos] (auto writ)
  }
};
#endif
//---------------------------------------------------
// File writer, iovec vectored output, double-bufferred 
// (non-vectored writes have low throughput on my ext4 setup).
// Gen: Generator function with size() and count() members
// n_iovs:  Number of iov in an iovec batch
// iovsize: Number of bytes in each iov buffer
template <typename Gen, typename Buf=iov_buffers<typename Gen::value_type>>
future<> write_filev(const sstring& filename)
{
  using Rec = typename Gen::value_type;
  //constexpr size_t size = Gen::size()*sizeof(Rec);
  auto oflags = open_flags::rw | open_flags::create | open_flags::exclusive;
  // extend in 16M allocations, sloppy_size=true, target size hint
  //file_open_options foo{ 1<<24, true, size};

  auto wf = open_file_dma(filename, oflags/*, foo*/);//.then([] (file f) mutable {
  //   std::cout << "File opened.\nTruncating file to " << Gen::size()*sizeof(Rec) << std::endl;
  //   return f.truncate(Gen::size()*sizeof(Rec)).then([&f](){return f;}); // allocate ?
  // });
  using poslen2 = std::array<pos_len,2>;
  return do_with( file{}, semaphore{0}, Gen{}, Buf{2}, poslen2{},
                  [&filename, wf=std::move(wf)]
                  (file& f, semaphore& inc, Gen& gen, Buf& bufs, poslen2& pl) mutable
  {
    pl = {fill(bufs[0],gen),fill(bufs[1],gen)};

    wf.then([&f, &inc, &gen, &bufs, &pl] (file of)
    {
      f = std::move(of);
      for (unsigned b=0; b!=2; ++b)
      {
        repeat([&f, &inc, &gen, &buf=bufs[b], &pl=pl[b]] () mutable
        {
          return f.dma_write(pl.pos, iov(buf,pl.len))
                  .then([&inc, &gen, &buf, &pl] (auto writ) mutable
          {
            size_t recs_writ = writ/sizeof(Rec);
            assert(recs_writ == pl.len);
            bool stop = pl.len<std::size(buf) || (pl=fill(buf,gen)).len==0;
            inc.signal(recs_writ);
            return make_ready_future<stop_iteration>(stop);
          });
        });
      }
    });
    
    return inc.wait(gen.size()).then([&f] () mutable {
      return f.flush(); }).then([&f] () mutable {
      return f.close(); }).then([] {
      return make_ready_future<>();
    });
  });
}

/*
// Single dma_read into one big allocation
template <typename Gen, typename Buf=iov_buffers<typename Gen::type>>
future<> read_filev(const sstring& filename)
{
  using Rec = typename Gen::type;

  return do_with( file{}, Gen {}, Buf{},
     [&filename] (file& f, Gen& gen, Buf& buf) mutable
  {
    auto oflags = open_flags::ro | open_flags::exclusive;
    return open_file_dma(filename, oflags).then([&f, &gen, &buf] (file of)
    {
      std::cout << "\nOpened file";
      f = std::move(of);

      return f.dma_read(buf.bget(0), buf.iov(0))
              .then([&f, fsize, &buf] (auto w) 
      {
        std::cout << "\nRead " << w << " bytes of " << fsize << '\n';
        assert(w == fsize);
        std::cout << "\nClosing file and freeing buffer\n";
        return f.close();
      });
    });
  });
}
*/
/***************************************************************************/
// Sorting functions
// Components for sorting large arrays of large fixed-length data records
// => Sort data indices rather than data records
// => Sort by radix from most significant (MS) end,
//                  depth-first or breadth-first
//
// index_radix_sort_??(array of N records) -> array of N permuted indices.
// Given an array of records, return indices of the array in sorted order.
//
// Radix sort on record[i] values i=0,1,2,...,N-1 only as deep as needed.
// Depth-first decends equal subranges fully before continuing to the next one.
// Breadth-first sorts each depth level fully before going deeper as needed.
// Assumes/requires index operator[] for lexicographic comparison.

// Depth-first index radix sort, recursive helper implementation
template <typename Array, size_t N=size(Array{}),
          typename index=uint_least_t<N-1>,
          typename indices=std::array<index,N>>
void recurse_index_radix_sort_df( Array const& data, indices& inds,
                                  unsigned level, index b, index e)
{
  std::sort(&inds[b], &inds[e], [&data,level] (index const& l, index const& r)
                                { return data[l][level] < data[r][level]; });
  if ((level+1)!=N)
  {   // find equal runs of 2 or more from the newly sorted range & sort 'em
    for (auto c=b; b!=e; b=c)
    {
      while (++c!=e && data[inds[c]][level]==data[inds[b]][level]);
      if (c>(b+1)) {
        recurse_index_radix_sort_df(data, inds, level+1, b, c);
      }
    }
  }
}

// Depth-first radix sort calling the recursive helper implementation
template <typename Array, size_t N=size(Array{}),
          typename index=uint_least_t<N-1>,
          typename indices=std::array<index,N>>
indices index_radix_sort_dfr( Array const& data)
{
  indices inds=iota<indices>();
  recurse_index_radix_sort_df(data, inds, 0u, index{0}, index{N});
  return inds;
}

// Depth-first radix sort, non recursive
template <typename Array, size_t N=size(Array{}),
          typename index=uint_least_t<N-1>,
          typename indices=std::array<index,N>>
indices index_radix_sort_df( Array const& data)
{
  indices inds{iota<indices>()};
  struct irange {size_t ibegin, icurr, iend;};
  for  (std::vector<irange> ranges{{0,0,N}}; !ranges.empty();)
  {
    size_t level{ranges.size()-1};
    auto& r = ranges.back();
    auto b = r.icurr;
    auto const e = r.iend;
    if (b==r.ibegin)
    {
      std::sort(&inds[b], &inds[e], [&data,level] (index const& l, index const& r)
                                    { return data[l][level] < data[r][level]; });
    }
    if ((level+1)<N)
    {   // find equal runs of 2 or more from the newly sorted range & sort 'em
      for (auto c=b; b!=e; b=c)
      {
        while (++c!=e && data[inds[c]][level]==data[inds[b]][level]);
        if (c>(b+1)) {
          r.icurr = c;
          ranges.push_back({b,b,c});
          break;
        }
      }
      if (b!=e) continue;
    }
    ranges.pop_back();
  }
  return inds;
}

// Breadth-first index radix sort
template <typename Array, size_t N=size(Array{}),
          typename index = uint_least_t<N-1>,
          typename indices=std::array<index,N>>
indices index_radix_sort( Array const& data)
{
  indices inds=iota<indices>();

  struct irange {size_t ibegin, iend;};
  std::vector<irange> curr_ranges{{0,N}};
  std::vector<irange> next_ranges;

  for (auto level=0; !curr_ranges.empty() && level!=N;
            ++level,  curr_ranges.swap(next_ranges), next_ranges.clear())
  {
    for (auto r : curr_ranges)
    {
      std::sort(&inds[r.ibegin], &inds[r.iend],
                [&data,level] (index const& a, index const& b)
                { return data[a][level] < data[b][level]; });
      // extract 'equal_range' runs of 2 or more from the newly sorted range
      for (auto ib=r.ibegin, ie=ib; ib!=r.iend; ib=ie)
      {
        while (++ie!=r.iend && data[inds[ie]][level]==data[inds[ib]][level]);
        if (ie>(ib+1)) {
          next_ranges.push_back({ib,ie});
        }
      }
    }
  }
  return inds;
}


//***********************************

// Given a data array and an array of indices into consecutive sorted partitions
// of size P, which must be specified as a template argument,
// return the full, merged, sorted array of indices.
// The merge maps permuted indices [0:Np),[0:Np)...[0:Npe) -> [0:N)
template <size_t P,  // P = partition size
          typename Data, typename Indices, size_t D=ssize(Data{})>
auto index_mergeKparts(Data const& data, Indices const& inds)
{
  static_assert( size(Data{}) == size(Indices{}),
                "Index array must be same size as data array");

  constexpr size_t K = (D+P-1)/P;    // K = number of partitions
  constexpr size_t PK = D - (K-1)*P; // PK = size of the final, Kth, partition

  using d_index = uint_least_t<D-1>; // index into the data / data indices
  using p_index = uint_least_t<P-1>; // index into a single partition
  using h_index = uint_least_t<K-1>; // index into an array of partitions

  std::array<d_index,D> out;
  std::array<p_index,K> headq{};
  std::array<h_index,K> heap{ iota<std::array<h_index,K>>()};

  auto index = [&inds,&headq](h_index i)->d_index {
                      return i*P + inds[i*P + headq[i]]; };

  auto cmp = [&data,&index] (h_index l, h_index r) {
                      return data[index(l)]>data[index(r)]; };

  auto const hb = std::begin(heap);
  std::make_heap(hb,std::end(heap), cmp);

  for (size_t di=0, hsize=K; di!=D; ++di)
  {
    h_index hq {heap[0]};
    out[di] = index(hq);
    std::pop_heap(hb, hb+hsize, cmp);
    if (headq[hq]!=(P-1) && ((hq!=K-1) || headq[hq]!=(PK-1) ))
    {
      ++headq[hq];
      std::push_heap(hb, hb+hsize, cmp);
    }
    else 
    {
      --hsize;
    }
  }
  return out;
}



future<> sort(const sstring& infile, const sstring& outfile)
{
  return do_with( file{}, file{}, [&infile,&outfile] (file& in, file& out)
  {
    auto const ro_excl = open_flags::ro | open_flags::exclusive;
    return open_file_dma(infile, ro_excl).then([&in,&out,&outfile] (file fin)
    {
      in = std::move(fin);
      in.size().then([&out,&outfile] (uint64_t size)
      {
        assert(size%P==0);
        //size_t const D = size/P; // data size; No. records in the input file
        //size_t const C{}; // cache size <=D
        //size_t const K = (D+P-1)/P; // number of partitions in the file
        //size_t const M = (C+P-1)/P; // number of partitions in the cache

        // extend in 256M allocations, sloppy_size, target size hint
        file_open_options foo{ 1<<28, true, size};
        auto const rw_excl = open_flags::rw | open_flags::exclusive
                                            | open_flags::create;
        auto wf = open_file_dma(outfile, rw_excl, foo).then([&out,size] (file fo) mutable {
          out = std::move(fo);
          // fo.truncate(size); // or allocate, or leave to file_open_options?
          return fo;
        });

      });
    });

  });
}

/*
  std::array<uint8_t,D> inds;
  for (d_index di=0, k=0; k!=K; ++k, di = ((di+P)<=D ? di+P : D))
  {
    //std::cout << di << ',';
    auto& indk = as_array<P>(std::begin(inds)+di);
    indk = index_radix_sort_df(as_array<P>(std::begin(data)+di));
  }
  auto indc = index_mergeKparts<P>(data,inds);
}
*/
// Restriction: the maximum number of 4K records in the file is 2^32,
// set by an implementation decision to use 32-bit record indexing.
// So, the maximum filesize is 16 TByte (2^32 * 2^12 = 2^44)
// requiring 2^34 = 16 GByte RAM to hold indices of the index

void add_program_options(app_template& app)
{
  namespace bpo = boost::program_options;
  app.add_options()
        ("records,N", bpo::value<int>()->default_value(16*1024*1024),
                                        "Number of 4K records")
        ("size,s", bpo::value<int>()->default_value(16), "size")
        ;
  app.add_positional_options({
       { "filename", bpo::value<sstring>()->default_value("data"),
         "data file", -1}
  });
}

using Rec = std::array<uint32_t,4>;

//constexpr size_t P = 256;   // partition size
constexpr size_t D = P*256; // data size
constexpr size_t K = (D+P-1)/P;      // K = number of partitions
constexpr size_t PK = D - (K-1)*P;   // PK = size of the final, Kth, partition

std::array<Rec,D> data;

void drec(Rec const& rec)
{
  for (auto const& e : rec) std::cout << ' '  << std::hex << std::setfill('0') << std::setw(8) << e;
}

void dump(auto const& inds, unsigned off=0)
{
    for (int i : inds) std::cout << std::dec << i << ',';
    std::cout << std::endl;
    for (int i : inds)
    {
        auto const& rec = data[i+off];
        drec(rec);
        std::cout << '\n';
    }
}

using d_index = uint_least_t<D-1>; // index into the data / data indices
using p_index = uint_least_t<P-1>; // index into a single partition of the data

int main(int argc, char** argv) 
{
#if 0
  std::random_device engine;
  for (auto& rec : data)
  {
    for (auto& e : rec)
      e = engine() & 0x0f;
  }
      
  std::cout << "Here we go" << std::endl;

  std::array<uint8_t,D> inds;
  for (d_index di=0, k=0; k!=K; ++k, di = ((di+P)<=D ? di+P : D))
  {
    //std::cout << di << ',';
    auto& indk = as_array<P>(std::begin(inds)+di);
    indk = index_radix_sort_df(as_array<P>(std::begin(data)+di));
  }
  auto indc = index_mergeKparts<P>(data,inds);
  std::cout << '\n' << indc.size() << std::endl;
  dump(as_array<8>(std::begin(indc)));
  dump(as_array<8>(std::end(indc)-8));

  std::cout << "done\n";
#endif

  app_template app;
  add_program_options(app);

  try
  {
    app.run(argc, argv, [&app]
    {
      auto& args = app.configuration();

      if (smp::count > 1)
      {
        return make_exception_future(std::runtime_error(
          "Only runs on one core for now: rerun with -c1 option.\n"));
      }
      auto stat = memory::stats();
      std::cout << stat.total_memory() << " total mem\n"
                << stat.free_memory() << " free mem\n";

      std::cout << "filesystem_has_good_aio_support: " << std::boolalpha
                << filesystem_has_good_aio_support(".",true) << '\n';
      //int N = args["records"].as<int>();
      sstring filename {args["filename"].as<sstring>()};
      std::cout << "filename: " << filename << '\n';



//     std::cout << "Writing file with " << Nrecs << " records, "
//               << Nrecs*4 << "K, " << Nrecs*sizeof(rec4K) << " bytes\n";
      using Gen = CountingGenerator<rec4K,1024
                                          //  ,rec4K::Reverse::yes
                                          //  ,rec4K::Explode::yes
                                          >;
      std::cout << "Gen size " << Gen::size() << '\n';
      return write_filev<Gen>(filename);
      // write_filev<Gen>(filename).then([filename]
      // {
      //   std::cout << "Done main" << std::endl;
      //   //return read_filev<Gen>(filename);
      //   return make_ready_future<>();
      // });
      //return read_file<Gen>(filename);
      //return make_ready_future<>();
    });
  }
  catch(std::exception& e)
  {
    std::cerr << "Failed to start application: "
              << std::current_exception() << "\n";
    return 1;
  }

  return 0;
}
