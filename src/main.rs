use num_bigint::{BigUint, BigInt, ToBigInt, ToBigUint, RandBigInt};
use num_traits::{Zero, One, FromPrimitive, ToPrimitive};
use num::integer::{lcm};
use std::cmp::Ordering;

fn cmp(a: &BigUint, b: u32) -> Ordering {
    let uintb = BigUint::from(b);
    if a < &uintb {
        Ordering::Less
    } else if a == &uintb {
        Ordering::Equal
    } else {
        Ordering::Greater
    }
}


// Implementation of the Rabin-Miller algorithm
// Returns true if n is probably prime or false if n is definitely composite
fn is_probable_prime(n: &BigUint, ntests: usize) -> bool {
    let mut rng = rand::thread_rng();
    let zero = BigUint::zero();
    let one = BigUint::one();
    let two = BigUint::from_u32(2).unwrap();
    let six = BigUint::from_u32(6).unwrap();

    if n < &six {
        // assuming n >= 0 in all cases... shortcut small cases here
        return [false, false, true, true, false, true][n.to_usize().unwrap()];
    } else if n % &two == zero { // maybe should use & 1 instead of % 2. & 1 should be faster than n % 2
        false
    } else {
        let mut s = BigUint::zero();
        let mut d = n - &one;
        while &d % &two == zero {
            s += &one;
            d = d >> 1; // d / 2 but faster;
        }
        for i in 0..ntests {
            let a = rng.gen_biguint_range(&two, &(n - &one));
            let mut x = a.modpow(&d, n);
            if x == one || x == n - &one {
                continue;
            }
            let mut r: BigUint = BigUint::zero();
            while r < s {
                x = x.modpow(&two, n);
                if x == one {
                    return false;
                } else {
                    break;
                }
                r += one;
            }
            if r == s {
                // None of the steps made x equal n-1.
                return false;
            }
        }
        return true;
    }
}

fn generate_prime() -> BigUint {
    // Receive this thread's random number generator
    let mut rng = rand::thread_rng();

    let mut p: BigUint;
    loop {
        // Generate a random BigUint integer 'p'
        p = rng.gen_biguint(2^64);

        // Return 'p' if 'p' is prime
        // FIX: is .clone() really necessary?
        if is_probable_prime(&p, 40) {
            break;
        }
    }

    p
}

// Iterative extended euclidean algorithm
// Assumes a and b are positive
// Returns (g, x, y) such that a*x + b*y = g = gcd(a, b)
fn xgcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let mut x = a.clone();
    let mut y = b.clone();
    let mut x0 = BigInt::one();
    let mut x1 = BigInt::zero();
    let mut y0 = BigInt::zero();
    let mut y1 = BigInt::one();
    let mut q = BigInt::zero();

    loop {
        q = &x / &y;
        x = &x % &y;

        x0 = x0 - &y0 * &q;
        x1 = x1 - &y1 * &q;
        if &x == &BigInt::from(0) {
            return (y, y0, y1);
        }
        q = &y / &x;
        y = &y % &x;

        y0 = y0 - &x0 * &q;
        y1 = y1 - &x1 * &q;
        if &y == &BigInt::from(0) {
            return (x, x0, x1);
        }
    }
}

fn modinverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let (g, x, _) = xgcd(a, m);
    if g != BigInt::one() {
        None
    }
    else {
        Some((x % m + m) % m)
    }
}

#[test]
fn test_xgcd() {
    let a = BigInt::from(65537);
    let b = BigInt::from(5175928221316961640 as u128);
    let (g,x,y) = xgcd(&a,&b);
    println!("({}, {}, {}) such that {}*{} + {}*{} = {} = gcd({}, {})", g,x,y,a,x,b,y,g,a,b);
    assert_eq!(g, BigInt::one(), "xgcd: g != 1. g={}", g);
    assert_eq!(x, BigInt::from(2476645758766476953 as u128), "xgcd: x != 2476645758766476953. x={}", x);
    assert_eq!(y, BigInt::from(-31359), "xgcd: y != -31359. y={}", y)
}
#[test]
fn test_is_probable_prime() {
    let prime_numbers = [
        "10167201030549713726441968717980102373".parse::<BigUint>().unwrap(),
        "10599361149869783661770394268978427307252044615855346733100106318222418164497".parse::<BigUint>().unwrap(),
        "10610513685219358207413288856303453790457009717189782578743788763678849011630362938798318315426990950760016868719337".parse::<BigUint>().unwrap(),
        "6085224155137788143682969993316862158915497708674162597743324400760854671028855684540763205768458936280440740362620969575458468469712885667218768590469943".parse::<BigUint>().unwrap(),
        "137524093296074949036040946273992015091264539903018995399021739161289874587198181126011613235336978436658346727494480662478222525673932719802389277480392845136725905981649573638379368380183555208117573983469857651660378659723865414946321961218133495901216755778412721276438005529598749113531263697562330224437".parse::<BigUint>().unwrap()
    ];
    for prime in &prime_numbers {
        assert!(is_probable_prime(prime, 40), "{} is a prime number but our test returns that it isn't", prime);
    }
    let non_primes = [
        "4".parse::<BigUint>().unwrap(),
        "6".parse::<BigUint>().unwrap(),
        "8".parse::<BigUint>().unwrap(),
        "120000000000000000000000000".parse::<BigUint>().unwrap(),
        "137524093296074949036040946273992015091264539903018995399021739161289874587198181126011613235336978436658346727494480662478222525673932719802389277480392845136725905981649573638379368380183555208117573983469857651660378659723865414946321961218133495901216755778412721276438005529598749113531263697562330224438".parse::<BigUint>().unwrap()
    ];
    for non_prime in &non_primes {
        assert!(!is_probable_prime(non_prime, 40), "{} is not a prime number but our test returns that it is", non_prime);
    }
}

fn main() {
    println!("rsa");
    println!("computing...");
    // Choose p
    let p: BigUint = generate_prime();
    println!("p={}", p);
    // Choose q
    let q: BigUint = generate_prime();
    println!("q={}", q);
    // Compute n = p * q
    let n: BigUint = &p * &q;
    println!("n={}", n);

    // Compute λ(n), where λ is Carmichael's totient function.
    // Since n = pq, λ(n) = lcm(λ(p),λ(q)), and since p and q are prime, λ(p) = φ(p) = p − 1 and likewise λ(q) = q − 1.
    // Hence λ(n) = lcm(p − 1, q − 1).
    let lambda_n = lcm(&p - BigUint::one(), &q - BigUint::one());
    println!("λ(n)={}", lambda_n);

    // Choose an integer e such that 1 < e < λ(n) and gcd(e, λ(n)) = 1; that is, e and λ(n) are coprime.
    // I've chosen an industry standard e, will always be coprime with whatever λ(n) is because it's a Fermat prime.
    let e: BigUint = BigUint::from_u64(65537).unwrap();
    println!("e={}", e);

    let d = modinverse(&BigInt::from(e), &BigInt::from(lambda_n)).unwrap();
    println!("d={}", d);
    println!("...done!");
}
