// Seastar "external sort" coding challenge, Will Wray Feb 2017
//
// Test files

#include "core/app-template.hh"
#include "core/file.hh"
#include "core/reactor.hh"
#include "core/semaphore.hh"

#include <boost/iterator/counting_iterator.hpp>

#include <algorithm>
#include <array>
#include <cstdint>

 static constexpr size_t fourK {4096U};
// 4-kbyte fixed length records, 4x1024 = 2^12 bytes, 2^15 bits,
//         64x64-byte cachelines, only 8 fit in 32K L1 data cache
// Good for disk 4k sector size alignment and DMA, but...
// want to avoid 4k-aliasing cache collisions on coherent
// strided accesses to a contiguous sequence of 4K records.
// -> Deliberately mis-align the data when read into RAM?

// rec4k, access as a std::array of bytes or 16/32/64-bit words.
// std array comparison is lexicographic (hopefully optimized)
union rec4K
{
  std::array< uint8_t,  fourK>   byte;
  std::array< uint16_t, fourK/2> ui16;
  std::array< uint32_t, fourK/4> ui32;
  std::array< uint64_t, fourK/8> ui64;
  uint8_t& operator[](int i) { return byte[i]; }
};
static_assert(sizeof(rec4K)==fourK ,"");

struct filer {
    filer(file&& f=file()) : f(std::move(f)) {}
    //filer& operator=(file&& f) : f(std::move(f)) {}
    //auto& operator->() { return &f; }
    file f;
};

//---------------------------------------------------
// generate data file using dma writes
future<> generate_datafile( sstring filename, int N) 
{
  static thread_local file f;
  static thread_local semaphore count{0};
  static thread_local semaphore buffs{64};

  return open_file_dma(filename, open_flags::wo | open_flags::create).then([N] (file fl)
  {
    std::cout << "** file opened\n";
    f = std::move(fl);
    //filer* f = &tlf;
    //auto f = new filer{std::move(fl)};
    std::cout << "**file moved\n";
    auto wbuf = allocate_aligned_buffer<unsigned char>(4096, 4096);
    const char hello[]{"hello"};
    std::copy(std::begin(hello),std::end(hello),wbuf.get());
    std::cout << "buffer content:" << wbuf.get() << '\n';
    auto wb = wbuf.get();
    f.dma_write(0,wb,4096).then([wbuf = std::move(wbuf)] (size_t bytes)
    {
      std::cout << "wrote " << bytes << "bytes\n";
      return count.signal(1);
    });
    return count.wait(1).then([] () mutable
    {
      std::cout << "got signal, flushing\n";
      return f.flush().then([] { f.close(); });
    }).finally([] {
      std::cout << "and finally************\n";
      f = std::move(file());
      std::cout << "**done and deleted, file wrote\n";
    });
    return make_ready_future<>();
  });
}

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

int main(int argc, char** argv) 
{
  app_template app;
  add_program_options(app);

  std::cout << smp::count << " cores\n";
  try
  {
    app.run(argc, argv, [&app]
    {
      auto& args = app.configuration();
      int N = args["records"].as<int>();
      sstring filename {args["filename"].as<sstring>()};
      std::cout << "filename: " << filename << '\n';

      return generate_datafile(filename, N);
    });
  }
  catch(...)
  {
    std::cerr << "Failed to start application: "
              << std::current_exception() << "\n";
    return 1;
  }
  return 0;
}
