
#include <numeric>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <cmath>
#include <cstdio>
#include <cassert>
#include <stdexcept>
#include <limits>
#include <random>
#include <chrono>
#include <strsafe.h>
#include <intrin.h>

/* This a program to factorise any 64-bit number. It is designed to be efficient, 
but not use obscure non-standard libraries. Some code is adapted from open-source
code. 
The progam uses trial division to find small factors, and Pollard's Rho algorithm
to find larger factors. This is faster than relying solely on trial division, and
avoids a large unwieldy list of prime numbers.
A list of the 1st  192725 prime numbers is generated using the Sieve of Eratosthenes. 
This list is used for trial division. If the residue after trial division is not prime,
Pollard's Rho algorithm is used to find the remaining factors.

A version of the Miller-Rabin primality test is used to check whether the residue
after trial division is prime or composite. 

The program assumes that the longest integers available are 64-bit.
A couple of "intrinsics" are used to handle 128-bit numbers during modular
multiplication and division, so that 64-bit integer overflow is avoided.
These intrinsics are microsoft-specific, so if another compiler were used an
alternative method would need to be found. 
*/

#define ThrowExc(a)                              \
{												 \
    char mesg[180] = { 0 };					     \
     sprintf_s(mesg, sizeof(mesg), "%s %s line  %d in file %s ", a,  __func__, __LINE__, __FILE__); \
    throw std::range_error(mesg);                \
}


/* struct intended to contain a list of prime factors. 
note: a 64-bit number can have at most 15 unique prime fracors. */
struct factorsS {
    int factorcount;           // number of unique prime factors
    __int64 factorlist[19][2]; // prime factor, exponent
};

/* used for 128-bit integers */
struct uint128_t {
    uint64_t hi;
    uint64_t lo;
};

bool* primeFlags = NULL;
uint64_t* primeList = NULL;
unsigned int prime_list_count = 0;
uint64_t primeListMax = 0;


// time in format hh:mm:ss.msec
/* this version does not rely on any windows-specific functions */
/* see https://stackoverflow.com/questions/16077299/how-to-print-current-time-with-milliseconds-using-c-c11/66291527#66291527
*/
const char* myTimeP()
{
    using namespace std::chrono;
    using clock = system_clock;

    static char timestamp[15];   // time in format hh:mm:ss.msec
    const auto current_time_point{ clock::now() };  /* get current time */

    /* convert to time_t */
    const time_t current_time{ clock::to_time_t(current_time_point) };

    /* convert to tm struct */
    //const tm current_localtime{ *std::localtime(&current_time) };
    tm current_localtime;
    localtime_s(&current_localtime, &current_time);

    /* convert to time interval since start of epoch (1 Jan 1970) */
    const auto current_time_since_epoch{ current_time_point.time_since_epoch() };
    /* get number of milliseconds */
    const auto current_milliseconds{ duration_cast<milliseconds> (current_time_since_epoch).count() % 1000 };

    size_t offset = std::strftime(timestamp, sizeof(timestamp), "%T",
        &current_localtime);  /* get HH:MM:SS into timestamp */
    /* append milliseconds */
    sprintf_s(timestamp + offset, sizeof(timestamp) - offset, ".%03lld", current_milliseconds);
    return timestamp;
}

/* get floor(sqrt(n))*/
uint64_t llSqrt(const uint64_t n) {
    double root = std::sqrt((double)n);
    uint64_t  iroot = std::llround(root);
    while (iroot * iroot > n)
        iroot--;
    return iroot;
}

// return value of bit in array corresponding to x. false (0) indicates a prime number
bool getBit(const uint64_t x, const bool array[])
{
    return array[x / 2];
}

/* sets bit in 'array' corresponding to 'x' */
/* assume 'num' is odd. no bits are stored for even numbers */
static void setBit(const uint64_t x, bool array[]) {
    array[x / 2] = true;
    return;
}

// fast way to check for primes, but generatePrimes must have been called first.
// true indicates a prime number
bool isPrime2(unsigned __int64 num) {

    if (num == 1) return false;
    if (num == 2) return true;
    if ((num & 1) == 0) return false; // even numbers other than 2 are not prime
    return !primeFlags[num / 2];
}

/* use  sieve of Eratosthenes to generate a list of prime numbers */
void generatePrimes(uint64_t max_val) {
    uint64_t numsave = 0, count = 1, num = 3;
    size_t plist_size = 0;  // size of prime list
    uint64_t sqrt_max_val;

    if (primeListMax >= max_val)
        return;  // nothing to do if prime list already generated

    max_val += 63 - (max_val + 63) % 64;  // round up to next multiple of 64
    sqrt_max_val = llSqrt(max_val);

    /* initialise flags */

    if (primeFlags != NULL) delete[]primeFlags;	// if generatePrimes has been called before
    // clear out old prime list
//primeFlags = (uint32_t*)std::calloc((max_val / 16) + 1, 1);
    primeFlags = new bool[max_val / 2 + 1] { 0 };
    assert(primeFlags != NULL);

    // allocate storage for primeList if required
    {
        if (primeList != NULL) std::free(primeList);
        plist_size = (size_t)((double)max_val / (std::log((double)max_val) - 1)) * 102 / 100;
        // add 2% for safety
        primeList = (uint64_t*)std::malloc(plist_size * sizeof(uint64_t));
        assert(primeList != NULL);
        prime_list_count = 1;
        primeList[0] = 2;  // put 1st prime into list
    }

    while (num <= max_val)
    {
        if (!getBit(num, primeFlags))
        {   /* we have found a prime number */
            primeList[count] = num;
            count++;
            numsave = num;

            if (num <= sqrt_max_val)  /* check whether starting value for i is already
                                      more than max_val, while avoiding an integer overflow*/
                for (uint64_t i = num * num; i <= max_val; i += (num * 2))
                { /* mark all odd multiples of num in range as not prime */
                  /* starting value is num*num rather than num*3 because the flag bits for
                  multiples of num less than num*num are already set and using num*num
                  makes the program run significantly faster */
                    setBit(i, primeFlags);
                }
        }
        num += 2;	// advance to next possible prime
    }

    // after completing the while loop we have found all the primes < max_val
    printf_s("  prime %9lld is %11lld\n", count, numsave);
    
    primeList[count] = ULLONG_MAX;		// set end marker
    prime_list_count = (unsigned int)count;
    primeListMax = primeList[count - 1];
    return;
}

/* divide 128-bit number dividend by 64 bit divisor, get 128-bit quotient,
 and 64-bit remainder. avoids overflow problem  */
uint128_t divide_uint128_by_uint64(uint128_t dividend, uint64_t divisor,
    uint64_t* remainder) {
    uint128_t quotient = { 0, 0 };
    if (divisor == 0) {
        ThrowExc("Division by zero");
    }
    if (divisor == 1) {
        return dividend;
    }

    /* divisor > 1 */
    // Perform the division manually for uint128_t
    uint64_t carry;
    quotient.hi = dividend.hi / divisor;
    carry = dividend.hi % divisor;
    quotient.lo = _udiv128(carry, dividend.lo, divisor, remainder);
    return quotient;
}

/*  calculates (a * b) % mod taking into account that a * b might overflow 64-bit number */
unsigned __int64 modMult(const unsigned __int64 a, const unsigned __int64 b,
    const unsigned __int64 mod) {
    /* this version uses intrinsics for 128-bit arithmetic instead of gmp/MPIR
    extended precision functions */
    uint128_t prod, quot;
    uint64_t rem;
    /* prod (128-bit) = a*b */
    prod.lo = _umul128(a, b, &prod.hi);

    /* rem = prod%m (quot value returned by divide is  not used) */
    quot = divide_uint128_by_uint64(prod, mod, &rem);

    return rem;
}

// calculate x^n%mod. Works even when intermediate result > 64-bits.
unsigned __int64 modPowerLL(const unsigned __int64 x, const unsigned __int64 np,
    unsigned __int64 mod) {
    /* this version uses intrinsics for 128-bit arithmetic instead of gmp/MPIR
   extended precision functions */
    unsigned __int64 n = np, p;  // p is a power of x
    uint128_t r = { 0, 1 };

    p = x;

    /* loop log2(n) times. Minimise number of modular multiplcations needed */
    while (n > 0) {
        if (n % 2 == 1) {
            r.lo = _umul128(r.lo, p, &r.hi); //    r *= p;

            // r %= mod;  (dividend is in r, remainder goes into r.lo, 
            // quotient is discarded)
            r.hi %= mod;   /* avoid possibility of integer overflow on divide,
                              without altering value of remainder. */
            _udiv128(r.hi, r.lo, mod, &r.lo);  /* divide r by mod. r.lo is set to remainder */
            r.hi = 0;    /* net result: r *= p (modulo mod) */
        }
        n /= 2;
        if (n == 0)
            break;
        // p = (p^2) %mod;
        p = modMult(p, p, mod);
    }
    return r.lo;
}

// n-1 = 2^s * d with d odd by factoring powers of 2 from n-1.
// returns true if n is is a strong probable prime to base d, otherwise false
static bool witness(unsigned __int64 n, unsigned int s, unsigned __int64 d,
    unsigned __int64 a)
{
    unsigned __int64 x = modPowerLL(a, d, n);   // calculate a^d%n
    unsigned __int64 y;

    while (s) {
        //y = (x * x) % n;
        y = modMult(x, x, n);		// do modular multiplication, works even if x*x would overflow
        //y %= n;
        if (y == 1 && x != 1 && x != n - 1)
            return false;
        x = y;
        --s;
    }
    if (y != 1)
        return false;
    return true;
}

/* Miller-Rabin primality test
* see https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test#Testing_against_small_sets_of_bases
check whether n is prime
* this test is deterministic up to 18,446,744,073,709,551,616 = 2^64
* if n <                  1,373,653,        it is enough to test a = 2 and 3;
* if n <                  9,080,191,        it is enough to test a = 31 and 73;
* if n <              4,759,123,141,        it is enough to test a = 2, 7, and 61;
* if n <          1,122,004,669,633,        it is enough to test a = 2, 13, 23, and 1662803;
* if n <          2,152,302,898,747,        it is enough to test a = 2, 3, 5, 7, 11;
* if n <          3,474,749,660,383,        it is enough to test a = 2, 3, 5, 7, 11, 13;
* if n <        341,550,071,728,321,        it is enough to test a = 2, 3, 5, 7, 11, 13, 17.
* if n <  3,825,123,056,546,413,051,        it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23.
* if n < 18,446,744,073,709,551,616 = 2^64, it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23,
*                                           29, 31, and 37
*/
static bool isPrimeMR(unsigned __int64 n)
{
    if (((!(n & 1)) && n != 2)          // if n is even & > 2 return false
        || (n < 2) 						// if n < 2 return false (i.e  if n=0 or 1)
        || (n % 3 == 0 && n != 3))		// if n is a multiple of 3 and not equal to 3 return false
        return false;

    // if n is 2 or 3 return true
    if (n <= 3)
        return true;
    // we have now established that n is an odd number > 3
    unsigned __int64 d = n / 2;  // note: n is odd, so 2*d = n-1
    unsigned int s = 1;

    /* get the position of the least significant 1 bit in d. If d were zero,
    result would be zero, and the value in s would be undefined, otherwise
    result is non-zero and s is the bit number of the least significant 1 bit in d.*/
    auto result = _BitScanForward64((unsigned long*)&s, d);  // for gcc compiler use __builtin_ctzll instead
    d >>= s;
    s++;

    // n-1 = 2^s * d with d odd by factoring powers of 2 from n-1
    if (n < 1373653)
        return witness(n, s, d, 2) && witness(n, s, d, 3);
    if (n < 9080191)
        return witness(n, s, d, 31) && witness(n, s, d, 73);
    if (n < 4759123141)
        return witness(n, s, d, 2) && witness(n, s, d, 7) && witness(n, s, d, 61);
    if (n < 1122004669633)
        return witness(n, s, d, 2) && witness(n, s, d, 13) && witness(n, s, d, 23)
        && witness(n, s, d, 1662803);
    if (n < 2152302898747)
        return witness(n, s, d, 2) && witness(n, s, d, 3) && witness(n, s, d, 5) && witness(n, s, d, 7)
        && witness(n, s, d, 11);
    if (n < 3474749660383)
        return witness(n, s, d, 2) && witness(n, s, d, 3) && witness(n, s, d, 5) && witness(n, s, d, 7)
        && witness(n, s, d, 11) && witness(n, s, d, 13);
    if (n < 341550071728321)
        return witness(n, s, d, 2) && witness(n, s, d, 3) && witness(n, s, d, 5) && witness(n, s, d, 7)
        && witness(n, s, d, 11) && witness(n, s, d, 13) && witness(n, s, d, 17);

    if (n < 3825123056546413051)
        return witness(n, s, d, 2) && witness(n, s, d, 3) && witness(n, s, d, 5) && witness(n, s, d, 7)
        && witness(n, s, d, 11) && witness(n, s, d, 13) && witness(n, s, d, 17) && witness(n, s, d, 19)
        && witness(n, s, d, 23);
    // the tests below are sufficient for any 64 bit number
    return witness(n, s, d, 2) && witness(n, s, d, 3) && witness(n, s, d, 5) && witness(n, s, d, 7)
        && witness(n, s, d, 11) && witness(n, s, d, 13) && witness(n, s, d, 17) && witness(n, s, d, 19)
        && witness(n, s, d, 23) && witness(n, s, d, 29) && witness(n, s, d, 31) && witness(n, s, d, 37);

}

/* get next prime > x  */
uint64_t nextP(uint64_t x) {
    x |= 1;   /* ensure x is odd */
    while (!isPrimeMR(x))
        x += 2;   /* loop until x is prime */
    return x;
}

/* get largest prime < x */
uint64_t prevP(uint64_t x) {
    if (x <= 3)
        return 2;  /* 2 is smallest prime */
    if ((x & 1) == 0)
        x--;    /* ensure x is odd */
    while (!isPrimeMR(x))
        x -= 2;   /* loop until x is prime */
    return x;
}

/* method to return prime divisor for n
adapted from:
https://www.geeksforgeeks.org/pollards-rho-algorithm-prime-factorization/
This method generally works.  */

// return (x^2 + c) % n; Correct result even when intermediate value exceeds 64 bits
uint64_t PRf(uint64_t x, uint64_t c, uint64_t n) {
    uint128_t rv = { 0,0 };
    uint64_t temp, result;
    temp = modMult(x, x, n);     // temp = x^2 mod n
    rv.lo = temp + c;
    if (rv.lo < temp)
        rv.hi++;       /* overflow i.e. carry > 0 */
    divide_uint128_by_uint64(rv, n, &result);  /* get remainder i.e. rv (mod n) in result */
#ifdef _DEBUG
    // if (rv.hi > 0)
   //     std::cout << "Prf(" << x << ", " << c << ", " << n << ") = " << result << "\n";
#endif
    return result;
}
uint64_t PollardRho(uint64_t n, int depth,
    unsigned int seed)
{
    long long ctr = 0;     /* loop counter*/
    /* no prime divisor for 1 */
    if (n == 1) return n;

    /* even number means one of the divisors is 2 */
    if (n % 2 == 0) return 2;

    /* initialize random seed */
    // distribute results between 1 and MAX inclusive.
    std::uniform_int_distribution<uint64_t> dist(1, ULONG_MAX); 

    std::mt19937_64 gen(seed);  // to seed mersenne twister.

    /* we will pick from the range [2, N) */

    uint64_t x, y;
    x = dist(gen);  // x is in range 1 to max
    x = x % (n - 2) + 2;  // x is in range 2 to n-1
    y = x;

    /* set the constant in f(x).
     * Algorithm can be re-run with a different c
     * if it throws failure for a composite. */
    uint64_t c = dist(gen);  // c is in range 1 to max
    c = c % (n - 1) + 1;  // c is in range 1 to n-1

    /* Initialize candidate divisor (or result) */
    uint64_t d = 1;

    /* until the factor is obtained. We expect to find a factor in less than 
    n^(1/4) itherations so less than 2^16 = 65536 iterations. */
    while (d == 1)   {
        /* Tortoise Move: x(i+1) = f(x(i)) */
        x = PRf(x, c, n);
   
        /* Hare Move: y(i+1) = f(f(y(i))) */
        y = PRf(y, c, n);
        y = PRf(y, c, n);

        /* check gcd of |x-y| and n */
        d = std::gcd(x > y ? (x - y) : (y - x), n);
  
        /* retry if the algorithm fails to find prime factor
         * with chosen x and c */
        if (d == n || ctr > 10'000'000) {
            ctr = 0;
            depth++;
            c = dist(gen);  // c is in range 1 to max
            c = c % (n - 1) + 1;  // c is in range 1 to n-1
            y = x;
        }
        ctr++;
    }

    if (ctr > 40'000 || depth > 0)  /* print message if more than normal 
             number of cycles was needed to get a factor */
        std::cout << "n= " << n << " ,d= " << d << " depth = " << depth
        << " ctr= " << ctr << " c = " << c << " seed = " << seed << '\n';
 
    return d;
}

/* get prime factors of tnum, using trial division and Pollard's Rho algorithm */
bool primeFactors(unsigned __int64 tnum, factorsS& f, const unsigned int SEED) {
    unsigned  int count = 0, i = 0;
    unsigned int seed;
 
    /* initialize random seed for pollard-rho */
    static std::random_device rd;   // non-deterministic generator
    if (SEED == 0)
        seed = rd();    /* use random seed */
    else
        seed = SEED;       /* seed is used if pollard-rho factorisation is used. */
   
    while (tnum > 1) {

        /* If possible, check whether tnum is prime?*/
        if (tnum <= primeListMax) {
            if (isPrime2(tnum)) { // this check is not essential. It's to save time
                f.factorlist[count][0] = tnum;
                f.factorlist[count][1] = 1;         // set exponent for this factor to 1
                f.factorcount = count + 1;
                return true;
            }
        }
        else {  // if tnum > primeListMax use another method to check if prime
            if (tnum < (primeList[i] * primeList[i])) {
                // logic here is that if tnum were not prime, it would
                // have at least 1 factor < primeList[i], which is is impossible
                // because all such factors have already been removed .
                f.factorlist[count][0] = tnum;
                f.factorlist[count][1] = 1;         // set exponent for this factor to 1
                f.factorcount = count + 1;
                return true;
            }
        }

        /* perform trial division*/
        if (tnum % primeList[i] == 0) {
            f.factorlist[count][0] = primeList[i];   // store prime factor of tnum
            f.factorlist[count][1] = 1;              // set exponent for this factor to 1
            tnum /= primeList[i];
            while (tnum % primeList[i] == 0) {
                f.factorlist[count][1]++;             // increase exponent
                tnum /= primeList[i];
            }
            count++;                                // increase count of unique factors
        }

        i++;										// move index to next prime

        if (i > prime_list_count) {  // all available primes used?
            if (isPrimeMR(tnum)) {
                f.factorlist[count][0] = tnum;
                f.factorlist[count][1] = 1;
                count++;
                break;
            }

            else if (cbrt(tnum) < primeListMax) {
                /* tnum now has no factors <= primeListMax, but it is not prime. Therefore
                it must have exactly two prime factors. We can use the Pollard Rho algorithm
                to get these factors.*/
                uint64_t factor;
                factor = PollardRho(tnum, 0, seed);
                assert(tnum % factor == 0);

                if (factor > 1) {
                    tnum /= factor;
                    /* save smaller factor 1st in factorlist */
                    if (factor < tnum) {
                        f.factorlist[count][0] = factor;
                        f.factorlist[count][1] = 1;
                        count++;
                        f.factorlist[count][0] = tnum;
                        f.factorlist[count][1] = 1;
                        count++;
                    }
                    else if (factor > tnum) {
                        f.factorlist[count][0] = tnum;
                        f.factorlist[count][1] = 1;
                        count++;
                        f.factorlist[count][0] = factor;
                        f.factorlist[count][1] = 1;
                        count++;
                    }
                    else { /* factor = tnum i.e. we have a perfect square */
                        f.factorlist[count][0] = tnum;
                        f.factorlist[count][1] = 2;
                        count++;
                    }
                    break;
                }
                else {
                    printf_s ("unable to factorise number (pollard Rho failed) \n");
                    f.factorcount = count;
                    return false;
                }
            }
            else {
                std::cout << "primeListMax = " << primeListMax << '\n';
                ThrowExc("unable to factorise number (too large)");
            }
        }

        /* drop through to here if there are still more primes to check as possible factors
        (so go round loop again) */
    }

    /* all factors have been found */
    f.factorcount = count;

    return true;
}

/* print the factors in f */
void printFactors(const factorsS &f) {
    for (int i = 0; i < f.factorcount; i++) {
        printf_s("%12lld ^ %2lld \n", f.factorlist[i][0], f.factorlist[i][1]);
    }
}

/* factorise n and print results */
void test(const uint64_t n, const unsigned int SEED, double &timeused) {
    factorsS flist;           /* list of factors */
    uint64_t temp = 1;
    clock_t start = clock();
    if (primeFactors(n, flist, SEED)) {   /* get factors */
        clock_t end = clock();
        std::cout << "factors of " << n << " are: \n";
        printFactors(flist);      /* print factors */
        double elapsed = ((double)end - start) / CLOCKS_PER_SEC;  /* time used in seconds */
        timeused += elapsed;
        printf_s("time used: %g seconds \n\n", elapsed);

        /* check that the factors are correct */
        for (int i = 0; i < flist.factorcount; i++) {
            for (int j = 1; j <= flist.factorlist[i][1]; j++)
                temp *= flist.factorlist[i][0];
        }
        if (temp != n)
            abort();   /* should never happen */
    }
    else std::cout << "unable to factorise " << n << '\n';
}

/* generate a number which is the product of 2 random primes */
uint64_t getTestNumber(void) {
    static int ctr = 0;
    uint64_t p1, p2, result, top_up;
    std::random_device rd;   // non-deterministic generator
    // distribute results between 1 and MAX inclusive.
    std::uniform_int_distribution<uint64_t> dist(1, ULONG_MAX);
    std::mt19937_64 gen(rd());  // to seed mersenne twister.
    p1 = dist(gen);
    p1 = nextP(p1);
    p2 = dist(gen);
    p2 = prevP(p2); 
    result = p1 * p2;
    top_up = ULLONG_MAX / result;
    result *= top_up;    /* top_up is small factors that should be found by 
                        trial division*/
    return result;
}

int main()
{/* quick demo that primeFactors actually works */
    uint64_t testlist[] = { 
                 6'981870'836329ULL,
            384367'769655'273281ULL,
            614889'782588'491410ULL,
          1'227627'036142'014151ULL,
          1'741450'190477'048101ULL,
          3'915183'677829'784007ULL,
          3'962572'984803'475573ULL,
          5'550259'199735'997319ULL,
          6'039645'314591'246447ULL,
          6'830008'274078'386699ULL,
          9'223372'036854'775807ULL,
         11'361084'498788'652497ULL,
         11'361084'663894'846053ULL,
         11'414308'641756'674389ULL,
         12'064627'686170'050711ULL,
         14'142414'403480'493114ULL,
         14'571452'135919'730967ULL,
         17'057202'237022'420927ULL,
         18'446743'979220'271189ULL, 
         18'446744'030759'878681ULL
    };
    double timeused = 0.0;
    try {
        clock_t start = clock();
        // generatePrimes(ULONG_MAX); /* this would take 30 seconds and a lot of memory, */
                                      /* Factorisation using just trial division
                                         would then be possible, but 100 times slower 
                                         than using Pollard's Rho. */
        generatePrimes(2642245);  // this is more than enough primes to factorise any 64-bit number
        clock_t end = clock();
        double elapsed = ((double)end - start) / CLOCKS_PER_SEC;  /* time used in seconds */
        printf_s("Prime list generated. Time used: %g seconds \n\n", elapsed);
        // system("PAUSE");  /* press any key to continue */

        for (int i = 1; i <= 10000; i++) {
            auto x = getTestNumber();   /* set x to number to factorise */
            test(x, 0, timeused);     /* factorise x, print factors. */
            //  system("PAUSE");  /* press any key to continue */
        }

        for (auto x : testlist)
            test(x, 0, timeused);  /* factorise x, print factors. */

        printf_s("total factorisation time = %g seconds \n", timeused);

        system("PAUSE");    /* press any key to continue*/
    }
    catch (const std::exception& e) {
        std::cout << " a standard exception was caught, with message: '"
            << e.what() << "'\n";
    }
}
