use rand::Rng;
use rand::prelude::ThreadRng;

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
    for _ in 0..10 {
        println!("prime {}", generate_prime());
    }
}
