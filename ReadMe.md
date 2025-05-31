This is a C++ program intended to factorise 64 bit numbers efficiently.

It uses trial division to find small factors, and Pollard's Rho to find 
larger factors. This is a compromise between simplicity and speed, as
Pollard's Rho is much faster for larger factors.

In order to imlement Pollard's Rho and the Miller-Rabin primality test we 
need modular exponentiation and modular multiplication, where the intermediate
product may be > 64 bits. Here this is done using intrinsics _udiv128
and _umul128. 

In order to port this to a compiler other than Visual Studio, it might be 
necessary to find another way to do this. For GCC using 128-bit integers
for these calculations might be possible.