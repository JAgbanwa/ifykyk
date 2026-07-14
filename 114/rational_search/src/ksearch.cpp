#include <gmpxx.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

namespace {

const mpz_class D1("7729484335457653901640057298531371241781");
const mpz_class D2("2486598372481845396683104279916570951657");
const mpz_class C("46620984167454969979069506324857826890656");
const mpz_class E("609530524018264138310326718615033307496");

const mpz_class P3("36");
const mpz_class P2("828206165581860705133665232912370284496880");
const mpz_class P1("6351161599146374737633882130250167287933965064228967875255393268381831015506756800");
const mpz_class P0("16234787638949931054338904909272730014525041302296577490759268200927073136776735826378161845204226655836573767036816415981");

const mpz_class EX_K1_NUM("-38342878036197254867299316338535661320806");
const mpz_class EX_K1_DEN("7729484335457653901640057298531371241781");
const mpz_class EX_K2_NUM("-3047652620091320691551633593075166537541");
const mpz_class EX_K2_DEN("12432991862409226983415521399582854758285");

struct Options {
    std::string mode = "box";
    mpz_class m_start = 0;
    mpz_class n_start = 0;
    mpz_class x_start = 0;
    std::uint64_t m_count = 0;
    std::uint64_t n_count = 0;
    std::uint64_t x_count = 0;
    std::uint64_t shard_index = 0;
    std::uint64_t shard_count = 1;
    std::uint64_t chunk = 1;
    std::uint64_t root_limit = 200000;
    std::uint64_t factor_trial_limit = 100000;
    std::uint64_t rho_attempts = 32;
    std::uint64_t rho_iters = 100000;
    std::uint64_t max_divisors = 10000000;
    std::uint64_t progress_every = 0;
    unsigned long q2_scale = 1;
    mpz_class scale = 1;
    mpz_class scale2 = 1;
    mpz_class scale3 = 1;
    mpz_class k2_den = D2;
    unsigned threads = std::max(1u, std::thread::hardware_concurrency());
    bool exclude_given = true;
    std::string out_path = "-";
};

struct SharedOutput {
    std::mutex mu;
    std::ofstream file;
    std::ostream* out = &std::cout;

    explicit SharedOutput(const std::string& path) {
        if (path != "-") {
            file.open(path, std::ios::out | std::ios::app);
            if (!file) {
                throw std::runtime_error("cannot open output file: " + path);
            }
            out = &file;
        }
    }

    void line(const std::string& s) {
        std::lock_guard<std::mutex> lock(mu);
        (*out) << s << '\n';
        out->flush();
    }
};

struct Stats {
    std::atomic<std::uint64_t> tested{0};
    std::atomic<std::uint64_t> hits{0};
    std::atomic<std::uint64_t> diagnostics{0};
};

[[noreturn]] void usage(const char* argv0) {
    std::cerr
        << "Usage:\n"
        << "  " << argv0 << " --mode box --m-start M --m-count N --n-start M --n-count N [options]\n"
        << "  " << argv0 << " --mode x --m-start M --m-count N --x-start X --x-count N [options]\n"
        << "  " << argv0 << " --mode divisors --m-start M --m-count N [options]\n\n"
        << "Options:\n"
        << "  --threads N                  worker threads\n"
        << "  --q2-scale N                 search k2 = n/(N*D2), default 1\n"
        << "  --shard-index I              zero-based shard index\n"
        << "  --shard-count N              number of shards\n"
        << "  --chunk N                    outer-loop chunk size, default 1\n"
        << "  --root-limit N               x-mode brute root modulus limit\n"
        << "  --factor-trial-limit N       divisor-mode trial division limit\n"
        << "  --rho-attempts N             divisor-mode Pollard-rho attempts\n"
        << "  --rho-iters N                divisor-mode Pollard-rho iterations per attempt\n"
        << "  --max-divisors N             divisor-mode safety cap\n"
        << "  --progress-every N           print stderr progress after N exact tests\n"
        << "  --out PATH                   output JSONL path, default stdout\n"
        << "  --no-exclude-given           do not suppress the pair named in the prompt\n";
    throw std::runtime_error("bad arguments");
}

mpz_class parse_mpz(const std::string& s) {
    mpz_class z;
    if (z.set_str(s, 10) != 0) {
        throw std::runtime_error("invalid integer: " + s);
    }
    return z;
}

std::uint64_t parse_u64(const std::string& s) {
    std::size_t pos = 0;
    unsigned long long v = std::stoull(s, &pos, 10);
    if (pos != s.size()) {
        throw std::runtime_error("invalid unsigned integer: " + s);
    }
    return static_cast<std::uint64_t>(v);
}

Options parse_args(int argc, char** argv) {
    Options opt;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto need = [&](const std::string& name) -> std::string {
            if (i + 1 >= argc) usage(argv[0]);
            ++i;
            (void)name;
            return argv[i];
        };

        if (a == "--mode") opt.mode = need(a);
        else if (a == "--m-start") opt.m_start = parse_mpz(need(a));
        else if (a == "--n-start") opt.n_start = parse_mpz(need(a));
        else if (a == "--x-start") opt.x_start = parse_mpz(need(a));
        else if (a == "--m-count") opt.m_count = parse_u64(need(a));
        else if (a == "--n-count") opt.n_count = parse_u64(need(a));
        else if (a == "--x-count") opt.x_count = parse_u64(need(a));
        else if (a == "--threads") opt.threads = static_cast<unsigned>(parse_u64(need(a)));
        else if (a == "--q2-scale") opt.q2_scale = static_cast<unsigned long>(parse_u64(need(a)));
        else if (a == "--shard-index") opt.shard_index = parse_u64(need(a));
        else if (a == "--shard-count") opt.shard_count = parse_u64(need(a));
        else if (a == "--chunk") opt.chunk = std::max<std::uint64_t>(1, parse_u64(need(a)));
        else if (a == "--root-limit") opt.root_limit = parse_u64(need(a));
        else if (a == "--factor-trial-limit") opt.factor_trial_limit = parse_u64(need(a));
        else if (a == "--rho-attempts") opt.rho_attempts = parse_u64(need(a));
        else if (a == "--rho-iters") opt.rho_iters = parse_u64(need(a));
        else if (a == "--max-divisors") opt.max_divisors = parse_u64(need(a));
        else if (a == "--progress-every") opt.progress_every = parse_u64(need(a));
        else if (a == "--out") opt.out_path = need(a);
        else if (a == "--no-exclude-given") opt.exclude_given = false;
        else if (a == "--help" || a == "-h") usage(argv[0]);
        else throw std::runtime_error("unknown option: " + a);
    }

    if (opt.threads == 0) opt.threads = 1;
    if (opt.q2_scale == 0) throw std::runtime_error("--q2-scale must be positive");
    if (opt.shard_count == 0) throw std::runtime_error("--shard-count must be positive");
    if (opt.shard_index >= opt.shard_count) throw std::runtime_error("--shard-index must be < --shard-count");
    if (opt.mode == "box") {
        if (opt.m_count == 0 || opt.n_count == 0) throw std::runtime_error("box mode needs positive --m-count and --n-count");
    } else if (opt.mode == "x") {
        if (opt.m_count == 0 || opt.x_count == 0) throw std::runtime_error("x mode needs positive --m-count and --x-count");
    } else if (opt.mode == "divisors") {
        if (opt.m_count == 0) throw std::runtime_error("divisors mode needs positive --m-count");
    } else {
        throw std::runtime_error("unknown --mode: " + opt.mode);
    }
    opt.scale = mpz_class(opt.q2_scale);
    opt.scale2 = opt.scale * opt.scale;
    opt.scale3 = opt.scale2 * opt.scale;
    opt.k2_den = opt.scale * D2;
    return opt;
}

mpz_class add_u64(const mpz_class& base, std::uint64_t off) {
    mpz_class z = base;
    mpz_add_ui(z.get_mpz_t(), z.get_mpz_t(), static_cast<unsigned long>(off));
    return z;
}

mpz_class abs_mpz(const mpz_class& z) {
    return z >= 0 ? z : -z;
}

mpz_class gcd_mpz(const mpz_class& a, const mpz_class& b) {
    mpz_class g;
    mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return g;
}

mpz_class p_of_m(const mpz_class& m) {
    return ((P3 * m + P2) * m + P1) * m + P0;
}

std::pair<std::string, std::string> reduced_fraction(mpz_class num, mpz_class den) {
    if (den < 0) {
        den = -den;
        num = -num;
    }
    mpz_class g = gcd_mpz(abs_mpz(num), den);
    num /= g;
    den /= g;
    return {num.get_str(), den.get_str()};
}

bool same_fraction(const mpz_class& a_num, const mpz_class& a_den,
                   const mpz_class& b_num, const mpz_class& b_den) {
    return a_num * b_den == b_num * a_den;
}

std::string json_quote(const std::string& s) {
    std::string out = "\"";
    for (char c : s) {
        if (c == '"' || c == '\\') {
            out.push_back('\\');
            out.push_back(c);
        } else if (c == '\n') {
            out += "\\n";
        } else {
            out.push_back(c);
        }
    }
    out.push_back('"');
    return out;
}

struct Hit {
    mpz_class y_abs;
    mpz_class rhs;
    mpz_class x_num;
    mpz_class x_den;
    mpz_class l_num;
    mpz_class l_den;
};

bool exact_test(const Options& opt, const mpz_class& m, const mpz_class& n,
                const mpz_class& p, Hit* hit) {
    const mpz_class x_num = opt.scale * E + n;
    if (x_num == 0) return false;

    const mpz_class required_mod = abs_mpz(x_num) / gcd_mpz(abs_mpz(x_num), opt.scale3);
    if (required_mod != 1 &&
        !mpz_divisible_p(p.get_mpz_t(), required_mod.get_mpz_t())) {
        return false;
    }

    const mpz_class l_num = opt.scale * (6 * m + C) + n;

    mpz_class num = l_num * l_num * x_num + opt.scale3 * p;
    mpz_class den = opt.scale2 * x_num;
    if (den < 0) {
        den = -den;
        num = -num;
    }

    if (!mpz_divisible_p(num.get_mpz_t(), den.get_mpz_t())) {
        return false;
    }

    mpz_class rhs;
    mpz_divexact(rhs.get_mpz_t(), num.get_mpz_t(), den.get_mpz_t());
    if (rhs < 0) return false;
    if (!mpz_perfect_square_p(rhs.get_mpz_t())) return false;

    if (opt.exclude_given) {
        if (same_fraction(m, D1, EX_K1_NUM, EX_K1_DEN) &&
            same_fraction(n, opt.k2_den, EX_K2_NUM, EX_K2_DEN)) {
            return false;
        }
    }

    mpz_class y;
    mpz_sqrt(y.get_mpz_t(), rhs.get_mpz_t());
    hit->y_abs = y;
    hit->rhs = rhs;
    hit->x_num = x_num;
    hit->x_den = opt.scale;
    hit->l_num = l_num;
    hit->l_den = opt.scale;
    return true;
}

std::string hit_json(const Options& opt, const std::string& mode,
                     const mpz_class& m, const mpz_class& n, const Hit& hit) {
    auto k1 = reduced_fraction(m, D1);
    auto k2 = reduced_fraction(n, opt.k2_den);
    auto x = reduced_fraction(hit.x_num, hit.x_den);
    auto l = reduced_fraction(hit.l_num, hit.l_den);

    std::ostringstream os;
    os << "{\"type\":\"hit\""
       << ",\"mode\":" << json_quote(mode)
       << ",\"q2_scale\":\"" << opt.q2_scale << "\""
       << ",\"m\":\"" << m.get_str() << "\""
       << ",\"n\":\"" << n.get_str() << "\""
       << ",\"k1_num\":\"" << k1.first << "\""
       << ",\"k1_den\":\"" << k1.second << "\""
       << ",\"k2_num\":\"" << k2.first << "\""
       << ",\"k2_den\":\"" << k2.second << "\""
       << ",\"x_num\":\"" << x.first << "\""
       << ",\"x_den\":\"" << x.second << "\""
       << ",\"linear_num\":\"" << l.first << "\""
       << ",\"linear_den\":\"" << l.second << "\""
       << ",\"rhs\":\"" << hit.rhs.get_str() << "\""
       << ",\"y_abs\":\"" << hit.y_abs.get_str() << "\""
       << "}";
    return os.str();
}

void maybe_progress(const Options& opt, Stats& stats) {
    if (opt.progress_every == 0) return;
    std::uint64_t t = stats.tested.load(std::memory_order_relaxed);
    if (t != 0 && t % opt.progress_every == 0) {
        static std::mutex progress_mu;
        std::lock_guard<std::mutex> lock(progress_mu);
        std::cerr << "tested=" << t << " hits=" << stats.hits.load() << '\n';
    }
}

std::pair<std::uint64_t, std::uint64_t> shard_bounds(std::uint64_t total, const Options& opt) {
    const std::uint64_t begin = static_cast<std::uint64_t>(
        (static_cast<unsigned __int128>(total) * opt.shard_index) / opt.shard_count);
    const std::uint64_t end = static_cast<std::uint64_t>(
        (static_cast<unsigned __int128>(total) * (opt.shard_index + 1)) / opt.shard_count);
    return {begin, end};
}

void run_box(const Options& opt, SharedOutput& output, Stats& stats) {
    const auto bounds = shard_bounds(opt.m_count, opt);
    const std::uint64_t shard_begin = bounds.first;
    const std::uint64_t shard_end = bounds.second;
    const std::uint64_t total = shard_end - shard_begin;
    std::atomic<std::uint64_t> next{0};

    auto worker = [&]() {
        while (true) {
            const std::uint64_t block = next.fetch_add(opt.chunk);
            if (block >= total) break;
            const std::uint64_t block_end = std::min<std::uint64_t>(total, block + opt.chunk);

            for (std::uint64_t local_i = block; local_i < block_end; ++local_i) {
                const mpz_class m = add_u64(opt.m_start, shard_begin + local_i);
                const mpz_class p = p_of_m(m);
                mpz_class n = opt.n_start;
                for (std::uint64_t j = 0; j < opt.n_count; ++j) {
                    Hit hit;
                    if (exact_test(opt, m, n, p, &hit)) {
                        stats.hits.fetch_add(1, std::memory_order_relaxed);
                        output.line(hit_json(opt, "box", m, n, hit));
                    }
                    stats.tested.fetch_add(1, std::memory_order_relaxed);
                    mpz_add_ui(n.get_mpz_t(), n.get_mpz_t(), 1);
                }
                maybe_progress(opt, stats);
            }
        }
    };

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < opt.threads; ++i) threads.emplace_back(worker);
    for (auto& t : threads) t.join();
}

std::uint64_t coeff_mod(const mpz_class& z, std::uint64_t mod) {
    return mpz_fdiv_ui(z.get_mpz_t(), static_cast<unsigned long>(mod));
}

std::uint64_t mul_mod(std::uint64_t a, std::uint64_t b, std::uint64_t mod) {
    return static_cast<std::uint64_t>((static_cast<unsigned __int128>(a) * b) % mod);
}

std::uint64_t p_mod_u(std::uint64_t r, std::uint64_t mod,
                      std::uint64_t c3, std::uint64_t c2,
                      std::uint64_t c1, std::uint64_t c0) {
    std::uint64_t v = (mul_mod(c3, r, mod) + c2) % mod;
    v = (mul_mod(v, r, mod) + c1) % mod;
    v = (mul_mod(v, r, mod) + c0) % mod;
    return v;
}

std::vector<std::uint64_t> roots_mod_bruteforce(std::uint64_t mod) {
    std::vector<std::uint64_t> roots;
    if (mod == 1) {
        roots.push_back(0);
        return roots;
    }
    const std::uint64_t c3 = 36 % mod;
    const std::uint64_t c2 = coeff_mod(P2, mod);
    const std::uint64_t c1 = coeff_mod(P1, mod);
    const std::uint64_t c0 = coeff_mod(P0, mod);
    for (std::uint64_t r = 0; r < mod; ++r) {
        if (p_mod_u(r, mod, c3, c2, c1, c0) == 0) roots.push_back(r);
    }
    return roots;
}

bool mpz_to_u64_if_small(const mpz_class& z, std::uint64_t* out) {
    if (z < 0) return false;
    if (!mpz_fits_ulong_p(z.get_mpz_t())) return false;
    unsigned long v = mpz_get_ui(z.get_mpz_t());
    *out = static_cast<std::uint64_t>(v);
    return true;
}

void test_one_x_candidate(const Options& opt, SharedOutput& output, Stats& stats,
                          const mpz_class& x_num, const mpz_class& m) {
    const mpz_class n = x_num - opt.scale * E;
    const mpz_class p = p_of_m(m);
    Hit hit;
    if (exact_test(opt, m, n, p, &hit)) {
        stats.hits.fetch_add(1, std::memory_order_relaxed);
        output.line(hit_json(opt, "x", m, n, hit));
    }
    stats.tested.fetch_add(1, std::memory_order_relaxed);
}

void run_x(const Options& opt, SharedOutput& output, Stats& stats) {
    const auto bounds = shard_bounds(opt.x_count, opt);
    const std::uint64_t shard_begin = bounds.first;
    const std::uint64_t shard_end = bounds.second;
    const std::uint64_t total = shard_end - shard_begin;
    std::atomic<std::uint64_t> next{0};

    auto worker = [&]() {
        while (true) {
            const std::uint64_t block = next.fetch_add(opt.chunk);
            if (block >= total) break;
            const std::uint64_t block_end = std::min<std::uint64_t>(total, block + opt.chunk);

            for (std::uint64_t local_i = block; local_i < block_end; ++local_i) {
                const mpz_class x_num = add_u64(opt.x_start, shard_begin + local_i);
                if (x_num == 0) continue;

                const mpz_class abs_x = abs_mpz(x_num);
                const mpz_class g = gcd_mpz(abs_x, opt.scale3);
                const mpz_class required_mod_mpz = abs_x / g;

                std::uint64_t required_mod = 0;
                if (required_mod_mpz == 1) {
                    for (std::uint64_t idx = 0; idx < opt.m_count; ++idx) {
                        const mpz_class m = add_u64(opt.m_start, idx);
                        test_one_x_candidate(opt, output, stats, x_num, m);
                    }
                } else if (mpz_to_u64_if_small(required_mod_mpz, &required_mod) &&
                           required_mod <= opt.root_limit) {
                    const std::vector<std::uint64_t> roots = roots_mod_bruteforce(required_mod);
                    const std::uint64_t start_rem =
                        mpz_fdiv_ui(opt.m_start.get_mpz_t(), static_cast<unsigned long>(required_mod));
                    for (std::uint64_t r : roots) {
                        std::uint64_t delta = (r + required_mod - start_rem) % required_mod;
                        for (std::uint64_t idx = delta; idx < opt.m_count; idx += required_mod) {
                            const mpz_class m = add_u64(opt.m_start, idx);
                            test_one_x_candidate(opt, output, stats, x_num, m);
                        }
                    }
                } else {
                    for (std::uint64_t idx = 0; idx < opt.m_count; ++idx) {
                        const mpz_class m = add_u64(opt.m_start, idx);
                        test_one_x_candidate(opt, output, stats, x_num, m);
                    }
                }
                maybe_progress(opt, stats);
            }
        }
    };

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < opt.threads; ++i) threads.emplace_back(worker);
    for (auto& t : threads) t.join();
}

std::vector<unsigned> primes_up_to(std::uint64_t limit) {
    if (limit < 2) return {};
    std::vector<bool> composite(limit + 1, false);
    std::vector<unsigned> primes;
    for (std::uint64_t p = 2; p <= limit; ++p) {
        if (!composite[p]) {
            primes.push_back(static_cast<unsigned>(p));
            if (p * p <= limit) {
                for (std::uint64_t q = p * p; q <= limit; q += p) composite[q] = true;
            }
        }
    }
    return primes;
}

mpz_class pollard_rho(const mpz_class& n, const Options& opt, std::uint64_t salt) {
    if (mpz_even_p(n.get_mpz_t())) return 2;
    for (std::uint64_t attempt = 1; attempt <= opt.rho_attempts; ++attempt) {
        mpz_class c(static_cast<unsigned long>(attempt + 17 * salt));
        mpz_class x(static_cast<unsigned long>(2 + attempt + salt));
        mpz_class y = x;
        mpz_class d = 1;

        auto step = [&](const mpz_class& z) {
            mpz_class v = (z * z + c) % n;
            if (v < 0) v += n;
            return v;
        };

        for (std::uint64_t iter = 0; iter < opt.rho_iters; ++iter) {
            x = step(x);
            y = step(step(y));
            mpz_class diff = abs_mpz(x - y);
            mpz_gcd(d.get_mpz_t(), diff.get_mpz_t(), n.get_mpz_t());
            if (d > 1 && d < n) return d;
            if (d == n) break;
        }
    }
    return 0;
}

struct FactorResult {
    std::vector<mpz_class> prime_factors;
    std::vector<mpz_class> unresolved;
};

void factor_rec(const mpz_class& value, const Options& opt, const std::vector<unsigned>& small_primes,
                FactorResult& result, std::uint64_t salt) {
    if (value <= 1) return;
    mpz_class n = value;

    for (unsigned p : small_primes) {
        if (n == 1) return;
        while (mpz_divisible_ui_p(n.get_mpz_t(), p)) {
            result.prime_factors.emplace_back(p);
            mpz_divexact_ui(n.get_mpz_t(), n.get_mpz_t(), p);
        }
    }

    if (n == 1) return;
    if (mpz_probab_prime_p(n.get_mpz_t(), 30) > 0) {
        result.prime_factors.push_back(n);
        return;
    }

    mpz_class d = pollard_rho(n, opt, salt);
    if (d == 0 || d == n) {
        result.unresolved.push_back(n);
        return;
    }
    factor_rec(d, opt, small_primes, result, salt + 1);
    factor_rec(n / d, opt, small_primes, result, salt + 2);
}

struct MpzLess {
    bool operator()(const mpz_class& a, const mpz_class& b) const {
        return mpz_cmp(a.get_mpz_t(), b.get_mpz_t()) < 0;
    }
};

std::map<mpz_class, unsigned, MpzLess> combine_factors(const std::vector<mpz_class>& factors) {
    std::map<mpz_class, unsigned, MpzLess> combined;
    for (const auto& f : factors) ++combined[f];
    return combined;
}

std::uint64_t divisor_count_capped(const std::map<mpz_class, unsigned, MpzLess>& factors,
                                   std::uint64_t cap) {
    unsigned __int128 total = 1;
    for (const auto& kv : factors) {
        total *= static_cast<unsigned __int128>(kv.second + 1);
        if (total > cap) return cap + 1;
    }
    return static_cast<std::uint64_t>(total);
}

template <typename Callback>
void enumerate_divisors_rec(std::vector<std::pair<mpz_class, unsigned>>& factors,
                            std::size_t idx, const mpz_class& current, Callback&& cb) {
    if (idx == factors.size()) {
        cb(current);
        return;
    }
    const mpz_class prime = factors[idx].first;
    const unsigned exp = factors[idx].second;
    mpz_class pow = 1;
    for (unsigned e = 0; e <= exp; ++e) {
        enumerate_divisors_rec(factors, idx + 1, current * pow, cb);
        pow *= prime;
    }
}

void emit_unfactored(const Options& opt, SharedOutput& output, Stats& stats,
                     const mpz_class& m, const mpz_class& target,
                     const std::vector<mpz_class>& unresolved) {
    std::ostringstream os;
    os << "{\"type\":\"unfactored\""
       << ",\"mode\":\"divisors\""
       << ",\"m\":\"" << m.get_str() << "\""
       << ",\"target_digits\":" << target.get_str().size()
       << ",\"unresolved\":[";
    for (std::size_t i = 0; i < unresolved.size(); ++i) {
        if (i) os << ',';
        os << "\"" << unresolved[i].get_str() << "\"";
    }
    os << "]}";
    output.line(os.str());
    stats.diagnostics.fetch_add(1, std::memory_order_relaxed);
    (void)opt;
}

void run_divisors(const Options& opt, SharedOutput& output, Stats& stats) {
    const std::vector<unsigned> small_primes = primes_up_to(opt.factor_trial_limit);
    const auto bounds = shard_bounds(opt.m_count, opt);
    const std::uint64_t shard_begin = bounds.first;
    const std::uint64_t shard_end = bounds.second;
    const std::uint64_t total = shard_end - shard_begin;
    std::atomic<std::uint64_t> next{0};

    auto worker = [&]() {
        while (true) {
            const std::uint64_t block = next.fetch_add(opt.chunk);
            if (block >= total) break;
            const std::uint64_t block_end = std::min<std::uint64_t>(total, block + opt.chunk);

            for (std::uint64_t local_i = block; local_i < block_end; ++local_i) {
                const mpz_class m = add_u64(opt.m_start, shard_begin + local_i);
                const mpz_class p = p_of_m(m);
                if (p == 0) {
                    std::ostringstream os;
                    os << "{\"type\":\"p_zero\",\"mode\":\"divisors\",\"m\":\"" << m.get_str()
                       << "\",\"note\":\"P(m)=0; k2 is infinite/arithmetic and must be handled separately\"}";
                    output.line(os.str());
                    stats.diagnostics.fetch_add(1, std::memory_order_relaxed);
                    continue;
                }

                const mpz_class target = abs_mpz(p) * opt.scale3;
                FactorResult fr;
                factor_rec(target, opt, small_primes, fr, local_i + 1);
                if (!fr.unresolved.empty()) {
                    emit_unfactored(opt, output, stats, m, target, fr.unresolved);
                    continue;
                }

                auto factor_map = combine_factors(fr.prime_factors);
                const std::uint64_t divisor_count = divisor_count_capped(factor_map, opt.max_divisors);
                if (divisor_count > opt.max_divisors) {
                    std::ostringstream os;
                    os << "{\"type\":\"too_many_divisors\",\"mode\":\"divisors\",\"m\":\"" << m.get_str()
                       << "\",\"cap\":" << opt.max_divisors << "}";
                    output.line(os.str());
                    stats.diagnostics.fetch_add(1, std::memory_order_relaxed);
                    continue;
                }

                std::vector<std::pair<mpz_class, unsigned>> factors(factor_map.begin(), factor_map.end());
                enumerate_divisors_rec(factors, 0, mpz_class(1), [&](const mpz_class& d) {
                    for (int sign : {1, -1}) {
                        const mpz_class x_num = sign > 0 ? d : -d;
                        const mpz_class n = x_num - opt.scale * E;
                        Hit hit;
                        if (exact_test(opt, m, n, p, &hit)) {
                            stats.hits.fetch_add(1, std::memory_order_relaxed);
                            output.line(hit_json(opt, "divisors", m, n, hit));
                        }
                        stats.tested.fetch_add(1, std::memory_order_relaxed);
                    }
                });
                maybe_progress(opt, stats);
            }
        }
    };

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < opt.threads; ++i) threads.emplace_back(worker);
    for (auto& t : threads) t.join();
}

}  // namespace

int main(int argc, char** argv) {
    try {
        Options opt = parse_args(argc, argv);
        SharedOutput output(opt.out_path);
        Stats stats;

        const auto start = std::chrono::steady_clock::now();
        if (opt.mode == "box") {
            run_box(opt, output, stats);
        } else if (opt.mode == "x") {
            run_x(opt, output, stats);
        } else if (opt.mode == "divisors") {
            run_divisors(opt, output, stats);
        }
        const auto end = std::chrono::steady_clock::now();
        const double seconds = std::chrono::duration<double>(end - start).count();
        std::cerr << "done mode=" << opt.mode
                  << " tested=" << stats.tested.load()
                  << " hits=" << stats.hits.load()
                  << " diagnostics=" << stats.diagnostics.load()
                  << " seconds=" << seconds << '\n';
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 2;
    }
}
