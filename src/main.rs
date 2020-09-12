use num_bigint::{BigUint, BigInt, ToBigInt, ToBigUint, RandBigInt};
use num_traits::{Zero, One};
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


// Transcription of the following pseudocode found in Wikipedia
/*
function is_prime(n)
    if n ≤ 3 then
        return n > 1
    else if n mod 2 = 0 or n mod 3 = 0
        return false

    let i ← 5

    while i × i ≤ n do
        if n mod i = 0 or n mod (i + 2) = 0
            return false
        i ← i + 6

    return true
 */
fn is_prime(n: &BigUint) -> bool {

    if cmp(n, 3) == Ordering::Less {
        return cmp(n, 1) == Ordering::Greater;
    } else if n % BigUint::from(2 as u8) == BigUint::zero() || n % BigUint::from(3 as u8) == BigUint::zero() {
        return false;
    }

    let mut i:BigUint = BigUint::from(5 as u8);
    while &i * &i <= *n {
        if n % &i == BigUint::zero() || n % (&i + BigUint::from(2 as u8)) == BigUint::zero() {
            return false;
        }
        i = i + BigUint::from(6 as u8);
    }

    return true;
}

fn generate_prime() -> BigUint {
    // Receive this thread's random number generator
    let mut rng = rand::thread_rng();

    let mut p: BigUint;
    loop {
        // Generate a random BigUint integer 'p'
        p = rng.gen_biguint(2^32);

        // Return 'p' if 'p' is prime
        // FIX: is .clone() really necessary?
        if is_prime(&p) {
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

// fn main() {
//     println!("running");
//     let a = BigInt::from(65537);
//     let b = BigInt::from(5175928221316961640 as u128);
//     let (g,x,y) = xgcd(&a,&b);
//     println!("({}, {}, {}) tal que {}*{} + {}*{} = {} = gcd({}, {})", g,x,y,a,x,b,y,g,a,b)
// }

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
    let lambda_n = lcm(&p - BigUint::from(1 as u8), &q - BigUint::from(1 as u8));
    println!("λ(n)={}", lambda_n);

    // Choose an integer e such that 1 < e < λ(n) and gcd(e, λ(n)) = 1; that is, e and λ(n) are coprime.
    // I've chosen an industry standard e, will always be coprime with whatever λ(n) is because it's a Fermat prime.
    let e: BigUint = BigUint::from(65537 as u32);
    println!("e={}", e);

    let d = modinverse(&BigInt::from(e), &BigInt::from(lambda_n)).unwrap();
    println!("d={}", d);
    println!("...done!");
}
