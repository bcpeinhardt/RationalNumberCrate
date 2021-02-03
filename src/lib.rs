//! Ben's Naive Rational Numbers Crate | Last Updated 2/2/2021
//! This crate serves as a basic implementation of a rational number structure. It aims to behave exactly
//! how you expect it to, and as many decisions about the structure as possible up to you.
//!

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};

#[derive(Debug)]
pub enum ComputationErr {
    DivByZeroErr,
}

/// The internal structure is just a numerator and denominator
/// Make them signed types if you want to have a negative number.
/// I know it seems like the fraction should be two unsigned ints and a sign flag but keep in mind that this is effectively a definition of
/// a rational number: An integer (which can be negative) divided by a non zero integer (which can also be negative)
#[derive(Debug, PartialEq)]
struct Rational<T>
where
    T: Add<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
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
        + Copy,
{
    // Public methods and associated functions

    /// The constructor for a rational takes a numerator and denominator
    pub fn from(n: T, d: T) -> Result<Self, ComputationErr> {
        use helpers::simplify_a_fraction;

        match simplify_a_fraction(n, d) {
            Ok((a, b)) => {
                return Ok(Rational { n: a, d: b });
            }
            Err(error) => {
                return Err(error);
            }
        }
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
        T: Sub<Output = T> + Rem<Output = T> + Div<Output = T> + PartialEq + Copy,
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
        T: Sub<Output = T> + Rem<Output = T> + PartialEq + Copy,
    {
        let zero = b - b;
        if a == zero {
            return b;
        } else {
            return gcd(b % a, a);
        }
    }

    // Least Common Denominator
    pub fn lcd<T>(a: T, b: T) -> Result<T, ComputationErr>
    where
        T: Sub<Output = T> + Div<Output = T> + Rem<Output = T> + Mul<Output = T> + PartialEq + Copy,
    {
        let zero = b - b;
        if b == zero {
            return Err(ComputationErr::DivByZeroErr);
        } else {
            return Ok(a * b / gcd(a, b));
        }
    }
}

#[cfg(test)]
mod helper_tests {
    // Tests the helper functions
    use super::helpers::*;

    #[test]
    fn simplify_algorithm_works() {
        assert_eq!(simplify_a_fraction(10, 10).unwrap(), (1, 1));
        assert_eq!(simplify_a_fraction(1, 10).unwrap(), (1, 10));
        assert_eq!(simplify_a_fraction(84, 49).unwrap(), (12, 7));
        assert_eq!(simplify_a_fraction(50, 25).unwrap(), (2, 1));
        assert!(simplify_a_fraction(17, 0).is_err());
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
