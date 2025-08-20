use malachite::base::num::arithmetic::traits::{AddMulAssign, Pow, UnsignedAbs};
use malachite::{Integer, Natural};
use ndarray::arr2;
use std::ops::{AddAssign, Div, MulAssign, SubAssign};
use std::panic;
use std::time::{Duration, Instant};

fn main() {

    for i in 20..27 {
        println!("Function 1:");
        let mut elapsed = Duration::from_secs(0);
        for _j in 0..4 {
            let start = Instant::now();
            optimized_fast_doubling(2u64.pow(i));
            elapsed += start.elapsed();
        }
        elapsed = elapsed.div(4);
        println!(
            "Fibonacci number (2^{}={}) in {:.2?}",
            i,
            2u64.pow(i),
            elapsed
        );

        println!("Function 2:");
        elapsed = Duration::from_secs(0);
        for _j in 0..4 {
            let start = Instant::now();
            optimized_fast_doubling_iterative(2u64.pow(i));
            elapsed += start.elapsed();
        }
        elapsed = elapsed.div(4);
        println!(
            "Fibonacci number (2^{}={}) in {:.2?}",
            i,
            2u64.pow(i),
            elapsed
        );
    }
}

fn test_helper(input: u64, expected_output: &str, fnb: fn(u64) -> Natural) {
    use std::str::FromStr;
    use std::{panic, sync::mpsc, thread, time::Duration};

    let (tx, rx) = mpsc::sync_channel(1);

    thread::spawn(move || {
        // catch panics inside the worker thread
        let result = panic::catch_unwind(|| fnb(input));
        let _ = tx.send(result);
    });

    match rx.recv_timeout(Duration::from_secs(1)) {
        Ok(Ok(result)) => {
            assert_eq!(result, Natural::from_str(expected_output).unwrap());
        }
        Ok(Err(_panic)) => {
            panic!("Test panicked (likely stack overflow) with input={}", input);
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("Test took over 1 second with input={}", input);
        }
        Err(e) => panic!("Worker-Thread-Fehler: {}", e),
    }
}

fn test_fibonacci(fnb: fn(u64) -> Natural) {
    test_helper(0, "0", fnb);
    test_helper(1, "1", fnb);
    test_helper(2, "1", fnb);
    test_helper(3, "2", fnb);
    test_helper(
        300,
        "222232244629420445529739893461909967206666939096499764990979600",
        fnb,
    );
    test_helper(
        1000,
        "4346655768693745643568852767504062580256466051737178040248172908953655\
        5417949051890403879840079255169295922593080322634775209689623239873322471161642996440\
        906533187938298969649928516003704476137795166849228875",
        fnb,
    );
    test_helper(
        10000,
        "3364476487643178326662161200510754331030214846068006390656476997468008\
        1442166662368155595513633734025582065332680836159373734790483865268263040892463056431\
        8873545443695598274916066020998841839338646527313000888302692356736131351175792974378\
        5441375213052050434770160226475831890652789085515436615958298727968298751063120057542\
        8783453215515103870818298969791613127856265033195487140214287532698187962046936097879\
        9003509623022910263681314931952756302278376284415403605844025721143349611800230912082\
        8704608892396232883546150577658327125254609359112820392528539343462090424524892940390\
        1706233888991085841065183173360437470737908552631764325733993712871937587746897479926\
        3058370657428301616374089691784263786242128352581128205163702980893320999057079200643\
        6742620238978311147005407499845925036063356093388383192338678305613643535189213327973\
        2908133732642652633989763922723407882928177953580570993691049175470808931841056146322\
        3382174656373212482263830921032977016480547262438423748624114530938122065649140327510\
        8664339451751216152654536133311131404243685480510676584349352383695965342807176877532\
        8348234345557366719731392746273629108210679280784718035329131176778924659089938635459\
        3278945237776744061922403376386740040213303432974969020283281459334188268176838930720\
        0363479562311710310129195316979460763273758925353077255237594378843450406771555577905\
        6450443016640119462580972216729758615026968443146952034614932291105970676243268515992\
        8347098912847067408620085871350162603120719031720860940812983215810772820763531866246\
        1127824553720853236530577595643007251774431505153960090516860322034916322264088524885\
        2433158051534849622434848299380905070483482449327453732624567755879089187190803662058\
        0095947431500524025327097469953187707243768259074199396322659841474981936092852239450\
        3970716544315642132815768890805878318340491743455627052022356484649519611246026831397\
        0975069382648706613264507665074611512677522748621598642530711298441182622661057163515\
        0692600298617049454250474913781151541399415506712562711971332527636319396069028956502\
        88268608362241082050562430701794976171121233066073310059947366875",
        fnb,
    );
    test_helper(100000, fast_doubling(100000).to_string().as_str(), fnb);
    test_helper(200000, fast_doubling(200000).to_string().as_str(), fnb);
    test_helper(500000, fast_doubling(500000).to_string().as_str(), fnb);
    test_helper(
        1_000_000,
        fast_doubling(1_000_000).to_string().as_str(),
        fnb,
    );
    test_helper(
        2_000_000,
        fast_doubling(2_000_000).to_string().as_str(),
        fnb,
    );
}

/// Calculates the nth Fibonacci number using an iterative approach.
///
/// This function computes the Fibonacci number for a given `n` in an
/// iterative manner, avoiding the overhead of recursion.
///
/// # Arguments
///
/// * `n` - The position of the Fibonacci number to compute as an `u128`.
///
/// # Returns
///
/// * The nth Fibonacci number as a `Natural`.
///
/// # Complexity
///
/// O(n).
fn iterative(n: u64) -> Natural {
    let mut x = Natural::from(0u128);
    let mut y = Natural::from(1u128);
    for _i in 1..n + 1 {
        let temp = x;
        x = y;
        y = temp + &x;
    }
    x
}

#[test]
fn test_iterative() {
    test_fibonacci(iterative);
}

/// Computes the nth Fibonacci number recursively.
///
/// # Arguments
///
/// * `n` - The position of the Fibonacci number to compute as an `u128`.
///
/// # Returns
///
/// * The nth Fibonacci number as a `Natural`.
///
/// # Panics
///
/// This function could cause a stack overflow for large values of `n` due to deep recursion.
///
/// # Complexity
///
/// O(2^n).
///
fn recursive(n: u64) -> Natural {
    if n > 1000 {
        panic!("Possible Stack overflow");
    }
    if n <= 1 {
        return Natural::from(n);
    }
    recursive(n - 1) + recursive(n - 2)
}

#[test]
fn test_recursive() {
    test_fibonacci(recursive);
}

fn tail_recursive(n: u64) -> Natural {
    if n > 9000 {
        panic!("Possible Stack overflow");
    }
    fn recursive_helper(n: u64, x: Natural, y: Natural) -> Natural {
        if n == 0 {
            return x;
        }
        recursive_helper(n - 1, y.clone(), x + y)
    }
    recursive_helper(n, Natural::from(0u128), Natural::from(1u128))
}

#[test]
fn test_tail_recursive() {
    test_fibonacci(tail_recursive);
}

/// Computes the nth Fibonacci number using matrix multiplication (naive approach).
///
/// This function uses a naive iterative approach to calculate the nth Fibonacci
/// number based on matrix exponentiation on the base Fibonacci matrix which when raised to a power
/// `n` effectively computes Fibonacci numbers using matrix properties.:
///
/// ```
/// | 1 1 |^n
/// | 1 0 |
/// ```
///
/// # Arguments
///
/// * `n` - The position of the Fibonacci number to compute as an `u128`.
///
/// # Returns
///
/// * The nth Fibonacci number as a `Natural`.
///
/// # Complexity
///
/// O(n)
fn matrix_naive(n: u64) -> Natural {
    if n == 0 {
        return Natural::from(0u128);
    }
    let a = arr2(&[
        [Natural::from(1u128), Natural::from(1u128)],
        [Natural::from(1u128), Natural::from(0u128)],
    ]);
    let mut w = Natural::from(1u128);
    let mut v = Natural::from(1u128);
    let mut x = Natural::from(1u128);
    let mut y = Natural::from(0u128);
    for _i in 1..n {
        let next_w = &w * &a[(0, 0)] + &v * &a[(1, 0)];
        let next_v = &w * &a[(0, 1)] + &v * &a[(1, 1)];
        let next_x = &x * &a[(0, 0)] + &y * &a[(1, 0)];
        let next_y = &x * &a[(0, 1)] + &y * &a[(1, 1)];
        w = next_w;
        v = next_v;
        x = next_x;
        y = next_y;
    }
    v
}

#[test]
fn test_matrix_naive() {
    test_fibonacci(matrix_naive);
}

fn matrix_short(n: u64) -> Natural {
    if n == 0 {
        return Natural::from(0u128);
    }
    let mut w = Natural::from(1u128);
    let mut v = Natural::from(1u128);
    let mut x = Natural::from(1u128);
    let mut y = Natural::from(0u128);
    for _i in 1..n {
        let next_w = &w + &v;
        let next_v = w;
        let next_x = &x + &y;
        let next_y = x;
        w = next_w;
        v = next_v;
        x = next_x;
        y = next_y;
    }
    v
}

#[test]
fn test_matrix_short() {
    test_fibonacci(matrix_short);
}

///Multiplies two 2x2 matrices using Strassen's Algorithm
fn matrix_mul_2x2(
    a1: &Integer,
    a2: &Integer,
    a3: &Integer,
    a4: &Integer,
    b1: &Integer,
    b2: &Integer,
    b3: &Integer,
    b4: &Integer,
    c1: &mut Integer,
    c2: &mut Integer,
    c3: &mut Integer,
    c4: &mut Integer,
) {
    let mut m1 = b1 + b4;
    m1.mul_assign(&(a1 + a4));

    let mut m2 = b3 + b4;
    m2.mul_assign(a1);

    let mut m3 = a2 - a4;
    m3.mul_assign(b1);

    let mut m4 = a3 - a1;
    m4.mul_assign(b4);

    let mut m5 = b1 + b2;
    m5.mul_assign(a4);

    let mut m6 = b3 - b1;
    m6.mul_assign(&(a1 + a2));

    let mut m7 = b2 - b4;
    m7.mul_assign(&(a3 + a4));

    *c1 = &m1 + &m4;
    c1.sub_assign(&m5);
    c1.add_assign(&m7);

    *c2 = &m3 + &m5;
    *c3 = &m2 + &m4;

    *c4 = &m3 + &m6;
    c4.add_assign(&m1);
    c4.sub_assign(&m2);
}

fn matrix_fast_exponentiation(n: u64) -> Natural {
    if n == 0 {
        return Natural::from(0u8);
    }

    // Base matrix: [[1,1],[1,0]]
    let mut a1 = Integer::from(1u8);
    let mut a2 = Integer::from(1u8);
    let mut a3 = Integer::from(1u8);
    let mut a4 = Integer::from(0u8);

    // Identity matrix
    let mut b1 = Integer::from(1u8);
    let mut b2 = Integer::from(0u8);
    let mut b3 = Integer::from(0u8);
    let mut b4 = Integer::from(1u8);

    let mut c1 = Integer::from(0u8);
    let mut c2 = Integer::from(0u8);
    let mut c3 = Integer::from(0u8);
    let mut c4 = Integer::from(0u8);

    let mut x = n;

    while x != 0 {
        if x & 1 != 0 {
            matrix_mul_2x2(
                &a1, &a2, &a3, &a4, &b1, &b2, &b3, &b4, &mut c1, &mut c2, &mut c3, &mut c4,
            );
            b1 = c1.clone();
            b2 = c2.clone();
            b3 = c3.clone();
            b4 = c4.clone();
        }

        matrix_mul_2x2(
            &a1, &a2, &a3, &a4, &a1, &a2, &a3, &a4, &mut c1, &mut c2, &mut c3, &mut c4,
        );
        a1 = c1.clone();
        a2 = c2.clone();
        a3 = c3.clone();
        a4 = c4.clone();

        x >>= 1;
    }
    b2.unsigned_abs()
}

#[test]
fn test_matrix_fast_exponentiation() {
    test_fibonacci(matrix_fast_exponentiation);
}

fn fast_doubling(n: u64) -> Natural {
    fn fib_pair(n: u64) -> (Natural, Natural) {
        if n == 0 {
            return (Natural::from(0u8), Natural::from(1u8));
        }
        let (mut a, b) = fib_pair(n >> 1);
        let mut c: Natural = (&b << 1) - &a;
        c.mul_assign(&a);
        let mut d = &a * &a;
        d.add_mul_assign(&b, &b);
        let mut e = c.clone();
        e.add_assign(&d);

        if n & 1 == 0 { (c, d) } else { (d, e) }
    }
    fib_pair(n).0
}

#[test]
fn test_fast_doubling() {
    test_fibonacci(fast_doubling);
}

fn optimized_fast_doubling(n: u64) -> Natural {
    fn fib_pair(n: u64) -> (Natural, Natural) {
        if n == 0 {
            return (Natural::from(0u8), Natural::from(1u8));
        }
        let (a, b) = fib_pair(n >> 1);

        if n & 1 == 0 {
            return (((&b << 1) - &a) * &a, a.pow(2) + b.pow(2));
        }
        let mut c: Natural = (&b << 1) - &a;
        c.mul_assign(&a);
        let d = a.pow(2) + b.pow(2);
        c.add_assign(&d);
        (d, c)
    }
    fib_pair(n).0
}

#[test]
fn test_optimized_fast_doubling() {
    test_fibonacci(optimized_fast_doubling);
}

fn optimized_fast_doubling_tail_recursive(n: u64) -> Natural {
    fn fib_pair(mask: u64, n: u64, a: Natural, b: Natural) -> Natural {
        if mask == 0 {
            return a;
        }
        if n & mask == 0 {
            fib_pair(mask >> 1, n, ((&b << 1) - &a) * &a, a.pow(2) + b.pow(2))
        } else {
            let mut c: Natural = (&b << 1) - &a;
            c.mul_assign(&a);
            let d = a.pow(2) + b.pow(2);
            c.add_assign(&d);
            fib_pair(mask >> 1, n, d, c)
        }
    }
    if n.is_power_of_two(){
        fib_pair(
            n,
            n,
            Natural::from(0u8),
            Natural::from(1u8),
        )
    }else{
        fib_pair(
            n.next_power_of_two() >> 1,
            n,
            Natural::from(0u8),
            Natural::from(1u8),
        )
    }
}

#[test]
fn test_optimized_fast_doubling_tail_recursive() {
    test_fibonacci(optimized_fast_doubling_tail_recursive);
}

fn optimized_fast_doubling_iterative(n: u64) -> Natural {
    if n == 0 {
        return Natural::from(0u8);
    }

    // Find starting mask = highest power of two <= n
    let mut mask = 1u64 << (63 - n.leading_zeros());

    let mut a = Natural::from(0u8); // F(0)
    let mut b = Natural::from(1u8); // F(1)

    while mask > 0 {
        if n & mask == 0 {
            // Even case
            let tmp_a = ((&b << 1) - &a) * &a;
            b = a.pow(2) + b.pow(2);
            a = tmp_a;

        } else {
            // Odd case
            let mut tmp_c: Natural = ((&b << 1) - &a) * &a;
            let tmp_d = a.pow(2) + b.pow(2);
            tmp_c += &tmp_d;
            a = tmp_d;
            b = tmp_c;
        }
        mask >>= 1;
    }

    a
}

#[test]
fn test_optimized_fast_doubling_iterative() {
    test_fibonacci(optimized_fast_doubling_iterative);
}
