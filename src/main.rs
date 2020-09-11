use rand::Rng;
use num::integer::{lcm};
use modinverse::modinverse;

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
fn is_prime(n: u32) -> bool {
    if n <= 3 {
        return n > 1;
    } else if n % 2 == 0 || n % 3 == 0 {
        return false;
    }

    let mut i = 5;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i = i + 6;
    }

    return true;
}

fn generate_prime() -> u32 {
    // Receive this thread's random number generator
    let mut rng = rand::thread_rng();

    let mut p: u32;
    loop {
        // Generate a random 32-bit integer 'p'
        p = rng.gen::<u32>();

        // Return 'p' if 'p' is prime
        if is_prime(p) {
            break;
        }
    }

    p
}

fn main() {
    // Choose p
    let p: u32 = generate_prime();
    println!("p={}", p);
    // Choose q
    let q: u32 = generate_prime();
    println!("q={}", q);
    // Compute n = p * q
    let n: u64 = (p as u64) * (q as u64);
    println!("n={}", n);

    // Compute λ(n), where λ is Carmichael's totient function.
    // Since n = pq, λ(n) = lcm(λ(p),λ(q)), and since p and q are prime, λ(p) = φ(p) = p − 1 and likewise λ(q) = q − 1.
    // Hence λ(n) = lcm(p − 1, q − 1).
    let lambda_n = lcm((p - 1) as u64, (q - 1) as u64);
    println!("λ(n)={}", lambda_n);

    // Choose an integer e such that 1 < e < λ(n) and gcd(e, λ(n)) = 1; that is, e and λ(n) are coprime.
    // I've chosen an industry standard e, will always be coprime with whatever λ(n) is because it's a Fermat prime.
    let e: u32 = 65537;
    println!("e={}", e);

    let d = modinverse(e as i128, lambda_n as i128).unwrap();
    println!("d={}", d as u64);
}
