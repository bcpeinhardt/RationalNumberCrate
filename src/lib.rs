//! Ben's Naive Rational Numbers Crate | Last Updated 2/3/2021
//!
//! This crate serves as a basic implementation of a fraction. It aims to behave exactly
//! how you expect it to, and leave as many decisions about the structure as possible up to you.
//!
//! +, +=, -, -=, *, *=, /, /= are all overloaded and .abs() and .pow(u32) methods are provided.
//! This data structure is exactly as likely to overflow as the datatype you base it on, so
//! be careful with pow(). There is also a rat![] macro.
//!
//! A rational number is defined as any number which can be represented as an integer divided by another
//! (but non zero) integer. This crate is MUCH less strict than that. All that is required to
//! create a "rational number", which is actually just a fraction, is that your type T implement the following traits:
//! Add<Output = T> + Mul<Output = T> + Sub<Output = T> + Rem<Output = T> + Div<Output = T> + PartialEq + PartialOrd + Copy
//!
//! That being said, please do not try to make a rational number out of floats, it will break everything, because many of
//! the algorithms involved in manipulation of the fraction require exact values (think gcd).
//!
//! This crate is designed to be used with primative data types for exact math operations. In the future I hope to make it
//! more robust so that it stands up to your custom data types.
//!
//! # Examples
//! ```
//! use bens_fractions::{Rational,rat};
//!
//! assert_eq!(rat![8i64, 32i64], Rational::from(8i64, 32i64).unwrap());
//! ```
//!

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};

/// This is just how I keep track of the idiots who divide by zero, your error will be a String.
#[derive(Debug)]
pub enum ComputationErr {
    DivByZeroErr,
}

/// The internal structure is just a numerator and denominator.
/// Make them signed types if you want to have a negative number.
/// I know it seems like the fraction should be two unsigned ints and a sign flag but keep in mind that this is effectively a definition of
/// a rational number: An integer (which can be negative) divided by a non zero integer (which can also be negative).
#[derive(Debug, Clone, Copy)]
pub struct Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    n: T,
    d: T,
}
impl<T> Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    // Public methods and associated functions

    /// The constructor for a rational: takes a numerator and denominator
    /// The type of the rational number is inferred from the input.
    ///
    /// # Examples
    /// ```
    /// use bens_fractions::Rational as Rat;
    ///
    /// let one_third = Rat::from(1i64, 3i64).unwrap();
    /// ```
    ///
    /// The type of the numerator must be the same as the type of the denominator.
    ///
    /// The constructor returns a result solely for the purpose of preventing people from creating
    /// fractions with zero denominators, because they are not by definition Rational. If this
    /// is too clunky for you, consider using the provided macro, which unwraps by itself.
    ///
    pub fn from(n: T, d: T) -> Result<Self, String> {
        use helpers::simplify_a_fraction;

        match simplify_a_fraction(n, d) {
            Ok((a, b)) => {
                return Ok(Rational { n: a, d: b });
            }
            Err(error) => {
                return Err(format!("{:?}", error));
            }
        }
    }

    /// Raises the fraction to the n power.
    /// # Panics
    /// This function will overflow based on the inner data type.
    /// If your fraction is based on u8, don't raise it to the 30th power.
    /// # Examples
    /// ```
    /// use bens_fractions::{Rational, rat};
    ///
    /// let two_thirds = Rational::from(-2, -3).unwrap();
    ///
    /// assert_eq!(two_thirds.pow(3), rat![8,27]);
    /// assert_eq!(two_thirds.pow(2), rat![4,9]);
    /// assert_eq!(two_thirds.pow(1), rat![2,3]);
    /// assert_eq!(two_thirds.pow(0), rat![1]);
    ///
    /// ```
    pub fn pow(&self, n: u32) -> Self {
        use helpers::simplify_a_fraction;

        if n == 0 {
            return Rational::from(self.n, self.n).unwrap();
        }

        let one = self.n / self.n;
        let mut num = one;
        let mut den = one;

        for _ in 0..n {
            num = num * self.n;
            den = den * self.d;
            if let Ok((a, b)) = simplify_a_fraction(num, den) {
                num = a;
                den = b;
            }
        }
        Rational::from(num, den).unwrap()
    }

    /// Takes the absolute value of the fraction. Numerator and denominator become positive.
    ///
    /// # Examples
    /// ```
    /// use bens_fractions::Rational;
    ///
    /// assert_eq!(
    ///        Rational::from(-2, 3).unwrap().abs(),
    ///        Rational::from(2, 3).unwrap()
    ///    );
    ///    assert_eq!(
    ///        Rational::from(-2, -3).unwrap().abs(),
    ///        Rational::from(2, 3).unwrap()
    ///    );
    ///    assert_eq!(
    ///        Rational::from(2, -3).unwrap().abs(),
    ///        Rational::from(2, 3).unwrap()
    ///    );
    ///    assert_eq!(
    ///        Rational::from(2, 3).unwrap().abs(),
    ///        Rational::from(2, 3).unwrap()
    ///    );
    /// ```
    /// 
    pub fn abs(&self) -> Self {
        let mut num = self.n;
        let mut den = self.d;

        let zero = self.d - self.d;
        if num < zero {
            num = num - (num + num);
        }
        if den < zero {
            den = den - (den + den);
        }

        Rational::from(num, den).unwrap()
    }

    // Internal methods

    // Call this guy any time we operate non trivially on the fraction
    fn simplify(&mut self) {
        use helpers::simplify_a_fraction;

        if let Ok((a, b)) = simplify_a_fraction(self.n, self.d) {
            self.n = a;
            self.d = b;
        }
    }
}

// Trait implementations

impl<T> PartialEq for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn eq(&self, rhs: &Self) -> bool {
        // I'm having a lot of trouble Identifying negatives with generics, and don't want to require a negative trait
        // so this is going to be a little hacky

        // If "a/b + a/b case, then num == num && denom == denom"
        // If -a/b + a/-b case, then num + num = zero, and denom + denom = zero

        let zero = self.n - self.n;
        (self.n == rhs.n && self.d == rhs.d) || (self.n + rhs.n == zero && self.d + rhs.d == zero)
    }
}

impl<T> PartialOrd for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn partial_cmp(&self, rhs: &Rational<T>) -> Option<std::cmp::Ordering> {
        use helpers::lcd;
        use std::cmp::Ordering;

        let zero = self.n - self.n;
        match (
            (self.n < zero && self.d > zero) || (self.n > zero && self.d < zero),
            (rhs.n < zero && rhs.d > zero) || (rhs.n > zero && rhs.d < zero),
        ) {
            // (neg/pos || pos/neg), (neg/pos || pos/neg)
            (true, false) => {
                return Some(Ordering::Less);
            }
            (false, true) => {
                return Some(Ordering::Greater);
            }
            (_, _) => {}
        }

        let lcd = lcd(self.d, rhs.d).unwrap();
        if (self.n * (lcd / self.d)) < (rhs.n * (lcd / rhs.d)) {
            return Some(Ordering::Less);
        } else if (self.n * (lcd / self.d)) > (rhs.n * (lcd / rhs.d)) {
            return Some(Ordering::Greater);
        } else if (self.n * (lcd / self.d)) == (rhs.n * (lcd / rhs.d)) {
            return Some(Ordering::Equal);
        }
        None
    }
}

// Operator overloads

/// Overload + operator for rational.
/// Returns a simplified fraction
impl<T> Add<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    type Output = Rational<T>;
    fn add(self, rhs: Self) -> Self {
        use helpers::lcd;

        let lcd = lcd(self.d, rhs.d).unwrap(); // Valid rats cannot have zero denoms so unwrap
        let num1 = self.n * (lcd / self.d); // 1/15 => 2/30
        let num2 = rhs.n * (lcd / rhs.d); // 1/10 => 3/30
        Rational::from(num1 + num2, lcd).unwrap()
    }
}

/// Overload += operator for rational.
/// Returns a simplified fraction
impl<T> AddAssign<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn add_assign(&mut self, rhs: Rational<T>) {
        use helpers::lcd;

        let lcd = lcd(self.d, rhs.d).unwrap(); // Valid rats cannot have zero denoms so unwrap
        let num1 = self.n * (lcd / self.d); // 1/15 => 2/30
        let num2 = rhs.n * (lcd / rhs.d); // 1/10 => 3/30
        self.n = num1 + num2;
        self.d = lcd;
    }
}

/// Overload - operator for rational.
/// Returns a simplified fraction
impl<T> Sub<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    type Output = Rational<T>;
    fn sub(self, rhs: Self) -> Self {
        use helpers::lcd;

        let lcd = lcd(self.d, rhs.d).unwrap(); // Valid rats cannot have zero denoms so unwrap
        let num1 = self.n * (lcd / self.d); // 1/15 => 2/30
        let num2 = rhs.n * (lcd / rhs.d); // 1/10 => 3/30
        Rational::from(num1 - num2, lcd).unwrap()
    }
}

/// Overload -= operator for rational.
/// Returns a simplified fraction
impl<T> SubAssign<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn sub_assign(&mut self, rhs: Self) {
        use helpers::lcd;

        let lcd = lcd(self.d, rhs.d).unwrap(); // Valid rats cannot have zero denoms so unwrap
        let num1 = self.n * (lcd / self.d); // 1/15 => 2/30
        let num2 = rhs.n * (lcd / rhs.d); // 1/10 => 3/30
        self.n = num1 - num2;
        self.d = lcd;
    }
}

/// Overload * operator for rational.
/// Returns a simplified fraction
impl<T> Mul<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    type Output = Rational<T>;
    fn mul(self, rhs: Self) -> Self {
        Rational::from(self.n * rhs.n, self.d * rhs.d).unwrap()
    }
}

/// Overload *= operator for rational.
/// Returns a simplified fraction
impl<T> MulAssign<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn mul_assign(&mut self, rhs: Self) {
        self.n = self.n * rhs.n;
        self.d = self.d * rhs.d;
        self.simplify();
    }
}

/// Overload / operator for rational.
/// Returns a simplified fraction
impl<T> Div<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    type Output = Rational<T>;
    fn div(self, rhs: Self) -> Self {
        Rational::from(self.n * rhs.d, self.d * rhs.n).unwrap()
    }
}

/// Overload /= operator for rational.
/// Returns a simplified fraction
impl<T> DivAssign<Rational<T>> for Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + PartialOrd
        + Copy,
{
    fn div_assign(&mut self, rhs: Self) {
        self.n = self.n * rhs.d;
        self.d = self.d * rhs.n;
        self.simplify();
    }
}

mod helpers {
    use super::*;
    use std::ops::{Add, Div, Mul, Rem, Sub};

    pub fn simplify_a_fraction<T>(a: T, b: T) -> Result<(T, T), ComputationErr>
    where
        T: Sub<Output = T>
            + Rem<Output = T>
            + Div<Output = T>
            + PartialEq
            + PartialOrd
            + Copy
            + Add<Output = T>,
    {
        let zero = b - b;
        if b == zero {
            return Err(ComputationErr::DivByZeroErr);
        }
        let gcd = gcd(a, b);
        Ok((a / gcd, b / gcd))
    }

    // Greatest Common Divisor
    pub fn gcd<T>(a: T, b: T) -> T
    where
        T: Sub<Output = T> + Rem<Output = T> + PartialEq + Copy + PartialOrd + Add<Output = T>,
    {
        let zero = b - b;
        if a == zero {
            return b;
        } else {
            return single_val_abs(gcd(b % a, a));
        }
    }

    // Least Common Denominator
    pub fn lcd<T>(a: T, b: T) -> Result<T, ComputationErr>
    where
        T: Sub<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + Mul<Output = T>
            + PartialEq
            + PartialOrd
            + Add<Output = T>
            + Copy,
    {
        let zero = b - b;
        if b == zero {
            return Err(ComputationErr::DivByZeroErr);
        } else {
            return Ok(single_val_abs(a * b / gcd(a, b)));
        }
    }

    fn single_val_abs<T>(val: T) -> T
    where
        T: Sub<Output = T> + PartialOrd + Add<Output = T> + Copy,
    {
        let zero = val - val;
        if val < zero {
            return val - (val + val);
        } else {
            return val;
        }
    }
}

/// The declarative macro is as simple as you can imagine it. The only purpose of the macro is
/// to make writing rationals easier. It skips the unwrap for you, so if you are are writing numbers,
/// use the macro. If you are parsing numbers, use the Rational::from() constructor so that you get
/// the error handling on zero denominators.
/// 
/// # Examples
/// ```
/// use bens_fractions::{Rational, rat};
/// 
/// assert_eq!(rat![2, 3], Rational::from(2, 3).unwrap());
/// assert_eq!(rat![5], Rational::from(5, 1).unwrap());
/// assert_eq!(rat![10u32, 12u32], Rational::from(5u32, 6u32).unwrap());
/// assert_eq!(rat![12i64, -6i64], Rational::from(-2i64, 1i64).unwrap());
/// ```
#[macro_export]
macro_rules! rat {
    ($num:expr, $den:expr) => {{
        Rational::from($num, $den).unwrap()
    }};
    ($num:expr) => {{
        Rational::from($num, $num / $num).unwrap()
    }};
}

#[cfg(test)]
mod macro_tests {
    use super::{rat, Rational};

    #[test]
    fn basic_macro_usage() {
        assert_eq!(rat![2, 3], Rational::from(2, 3).unwrap());
        assert_eq!(rat![5], Rational::from(5, 1).unwrap());
        assert_eq!(rat![10u32, 12u32], Rational::from(5u32, 6u32).unwrap());
        assert_eq!(rat![12i64, -6i64], Rational::from(-2i64, 1i64).unwrap());
    }

    #[test]
    fn macros_with_variables() {
        let two = 2;
        let three = 3;
        assert_eq!(rat![two, three], Rational::from(2, 3).unwrap());
    }
}

#[cfg(test)]
mod helper_tests {
    // Tests the helper functions
    use super::helpers::*;

    #[test]
    fn simplify_algorithm_works_positives() {
        // Positives
        assert_eq!(simplify_a_fraction(10, 10).unwrap(), (1, 1));
        assert_eq!(simplify_a_fraction(1, 10).unwrap(), (1, 10));
        assert_eq!(simplify_a_fraction(84, 49).unwrap(), (12, 7));
        assert_eq!(simplify_a_fraction(50, 25).unwrap(), (2, 1));

        // Div by zero err
        assert!(simplify_a_fraction(17, 0).is_err());
    }

    #[test]
    fn gcd_works() {
        assert_eq!(gcd(10, 15), 5);
        assert_eq!(gcd(15, 15), 15);
        assert_eq!(gcd(36, 24), 12);

        assert_eq!(gcd(-10, 15), 5);
        assert_eq!(gcd(15, -15), 15);
        assert_eq!(gcd(-36, -24), 12);
    }

    #[test]
    fn lcd_works() {
        assert_eq!(lcd(10, 15).unwrap(), 30);
        assert_eq!(lcd(15, 15).unwrap(), 15);
        assert_eq!(lcd(36, 24).unwrap(), 72);

        assert_eq!(lcd(-10, 15).unwrap(), 30);
        assert_eq!(lcd(15, -15).unwrap(), 15);
        assert_eq!(lcd(-36, -24).unwrap(), 72);
    }
}

#[cfg(test)]
mod rational_construction_tests {
    use super::Rational;
    // Test constructing a rational

    #[test]
    fn rational_from_different_unsigned_types() {
        assert_eq!(
            Rational::from(10u8, 5u8).unwrap(),
            Rational { n: 2u8, d: 1u8 }
        );

        assert_eq!(
            Rational::from(32u32, 8u32).unwrap(),
            Rational { n: 4u32, d: 1u32 }
        );
    }

    #[test]
    fn rational_from_different_signed_types() {
        assert_eq!(
            Rational::from(-30i64, 15i64).unwrap(),
            Rational { n: -2, d: 1 }
        );
        assert_eq!(
            Rational::from(-15i64, -20i64).unwrap(),
            Rational { n: 3, d: 4 }
        );
        assert_eq!(
            Rational::from(30i64, -15i64).unwrap(),
            Rational { n: -2, d: 1 }
        );
    }

    #[test]
    fn constructing_rational_with_zero_denominator_is_err() {
        assert!(Rational::from(77u64, 0u64).is_err());
    }
}

#[cfg(test)]
mod trait_implementation_tests {
    use super::Rational;

    #[test]
    fn partial_eq_trait_test() {
        assert!(Rational::from(1, 2).unwrap() == Rational::from(2, 4).unwrap());
        assert!(Rational::from(1, -2).unwrap() == Rational::from(-2, 4).unwrap());
    }

    #[test]
    fn partial_ord_trait_test() {
        assert!(Rational::from(2, 3).unwrap() > Rational::from(2, 4).unwrap());
        assert!(Rational::from(1, 3).unwrap() < Rational::from(2, 4).unwrap());

        assert!(Rational::from(-2, 3).unwrap() < Rational::from(2, 4).unwrap());
        assert!(Rational::from(1, 3).unwrap() > Rational::from(-2, 4).unwrap());
    }
}

#[cfg(test)]
mod operator_overload_tests {

    use super::Rational;
    // Tests for operator overloads

    #[test]
    fn add_overload() {
        // No simplifying
        let result = Rational::from(3, 17).unwrap() + Rational::from(5, 51).unwrap();
        assert_eq!(result, Rational::from(14, 51).unwrap());

        // Simplifying
        let result = Rational::from(3, 17).unwrap() + Rational::from(6, 51).unwrap();
        assert_eq!(result, Rational::from(5, 17).unwrap());
    }

    #[test]
    fn add_assign_overload() {
        // No simplifying
        let mut three_17ths = Rational::from(3, 17).unwrap();
        let five_51sts = Rational::from(5, 51).unwrap();
        three_17ths += five_51sts;
        assert_eq!(three_17ths, Rational::from(14, 51).unwrap());

        // Simplifying
        let mut three_17ths = Rational::from(3, 17).unwrap();
        three_17ths += Rational::from(6, 51).unwrap();
        assert_eq!(three_17ths, Rational::from(5, 17).unwrap());
    }

    #[test]
    fn sub_overload() {
        // No simplifying
        let result = Rational::from(3, 17).unwrap() - Rational::from(5, 51).unwrap();
        assert_eq!(result, Rational::from(4, 51).unwrap());

        // Simplifying
        let result = Rational::from(4, 17).unwrap() - Rational::from(6, 51).unwrap();
        assert_eq!(result, Rational::from(2, 17).unwrap());
    }

    #[test]
    fn sub_assign_overload() {
        // No simplifying
        let mut three_17ths = Rational::from(3, 17).unwrap();
        let five_51sts = Rational::from(5, 51).unwrap();
        three_17ths -= five_51sts;
        assert_eq!(three_17ths, Rational::from(4, 51).unwrap());

        // Simplifying
        let mut four_17ths = Rational::from(4, 17).unwrap();
        four_17ths -= Rational::from(6, 51).unwrap();
        assert_eq!(four_17ths, Rational::from(2, 17).unwrap());
    }

    #[test]
    fn mul_overload() {
        // No simplifying
        let two_thirds = Rational::from(2, 3).unwrap();
        let five_7ths = Rational::from(5, 7).unwrap();
        assert_eq!(two_thirds * five_7ths, Rational::from(10, 21).unwrap());

        // Simplifying
        let two_thirds = Rational::from(2, 3).unwrap();
        let five_halves = Rational::from(5, 2).unwrap();
        assert_eq!(two_thirds * five_halves, Rational::from(5, 3).unwrap());
    }

    #[test]
    fn mul_assign_overload() {
        // No simplifying
        let mut two_thirds = Rational::from(2, 3).unwrap();
        two_thirds *= Rational::from(5, 7).unwrap();
        assert_eq!(two_thirds, Rational::from(10, 21).unwrap());

        // Simplifying
        let mut two_thirds = Rational::from(2, 3).unwrap();
        two_thirds *= Rational::from(5, 2).unwrap();
        assert_eq!(two_thirds, Rational::from(5, 3).unwrap());
    }

    #[test]
    fn div_overload() {
        // No simplifying
        let two_thirds = Rational::from(2, 3).unwrap();
        let seven_5ths = Rational::from(7, 5).unwrap();
        assert_eq!(two_thirds / seven_5ths, Rational::from(10, 21).unwrap());

        // Simplifying
        let two_thirds = Rational::from(2, 3).unwrap();
        let two_5ths = Rational::from(2, 5).unwrap();
        assert_eq!(two_thirds / two_5ths, Rational::from(5, 3).unwrap());
    }
}

#[cfg(test)]
mod methods_tests {

    use super::Rational;

    #[test]
    fn pow() {
        let two_thirds = Rational::from(-2, -3).unwrap();
        assert_eq!(two_thirds.pow(3), Rational::from(8, 27).unwrap());
        assert_eq!(two_thirds.pow(2), Rational::from(4, 9).unwrap());
        assert_eq!(two_thirds.pow(1), Rational::from(2, 3).unwrap());
        assert_eq!(two_thirds.pow(0), Rational::from(1, 1).unwrap());
    }

    #[test]
    fn abs() {
        assert_eq!(
            Rational::from(-2, 3).unwrap().abs(),
            Rational::from(2, 3).unwrap()
        );
        assert_eq!(
            Rational::from(-2, -3).unwrap().abs(),
            Rational::from(2, 3).unwrap()
        );
        assert_eq!(
            Rational::from(2, -3).unwrap().abs(),
            Rational::from(2, 3).unwrap()
        );
        assert_eq!(
            Rational::from(2, 3).unwrap().abs(),
            Rational::from(2, 3).unwrap()
        );
    }
}
