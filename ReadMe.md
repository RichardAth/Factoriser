This is a C++ program intended to factorise 64 bit numbers efficiently.
This factoriser has been tested quite thoroughly. It is intended
as a compromise between speed and simplicity, and does not require
any libraries that are not part of standard C++.

It uses trial division to find small factors, and Pollard's Rho to find 
larger factors. This is a compromise between simplicity and speed, as
Pollard's Rho is much faster for larger factors. Typically it will 
factorise a 64-bit number in less than 0.02 seconds. 

The sieve of Eratosthenes is used to generate a list of prime numbers. 
The Miller-Rabin primality test is used, using bases suggested in
Wikipedia that should give a definitive result for numbers < 2^64.

In order to implement Pollard's Rho and the Miller-Rabin primality test we 
need modular exponentiation and modular multiplication, where the intermediate
product may be > 64 bits. Here this is done using intrinsics _udiv128
and _umul128. In order to port this to a compiler other than Visual Studio, 
it might be necessary to find another way to do this. For GCC using 
128-bit integers for these calculations should be possible.

The main function generates a lot of test numbers and factorises them.
The vast majority of the tests have 2 large primes as factors, which
are found using Pollard's rho algorithm.