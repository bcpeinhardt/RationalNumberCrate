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

// /// Overload += operator for rational.
// /// Returns a simplified fraction
// impl<T> AddAssign<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     fn add_assign(&mut self, addend: Rational<T>) {}
// }

// /// Overload - operator for rational.
// /// Returns a simplified fraction
// impl<T> Sub<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     type Output = Rational<T>;
//     fn sub(self, subtrahend: Self) -> Self {}
// }

// /// Overload -= operator for rational.
// /// Returns a simplified fraction
// impl<T> SubAssign<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     fn sub_assign(&mut self, subtrahend: Self) {}
// }

// /// Overload * operator for rational.
// /// Returns a simplified fraction
// impl<T> Mul<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     type Output = Rational<T>;
//     fn mul(self, multiplier: Self) -> Self {}
// }

// /// Overload *= operator for rational.
// /// Returns a simplified fraction
// impl<T> MulAssign<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     fn mul_assign(&mut self, rhs: Self) {}
// }

// /// Overload / operator for rational.
// /// Returns a simplified fraction
// impl<T> Div<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     type Output = Rational<T>;
//     fn div(self, divisor: Self) -> Self {}
// }

// /// Overload /= operator for rational.
// /// Returns a simplified fraction
// impl<T> DivAssign<Rational<T>> for Rational<T>
// where
//     T: Add<Output = T>
//         + Mul<Output = T>
//         + Sub<Output = T>
//         + Rem<Output = T>
//         + Div<Output = T>
//         + PartialEq
//         + Copy,
// {
//     fn div_assign(&mut self, divisor: Self) {}
// }

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
mod tests {

    // Test the helpers first
    use super::helpers::*;
    use super::*;

    #[test]
    fn simplify_algorithm_works() {
        assert_eq!(simplify_a_fraction(10, 10).unwrap(), (1, 1));
        assert_eq!(simplify_a_fraction(1, 10).unwrap(), (1, 10));
        assert_eq!(simplify_a_fraction(84, 49).unwrap(), (12, 7));
        assert_eq!(simplify_a_fraction(50, 25).unwrap(), (2, 1));
        assert!(simplify_a_fraction(17, 0).is_err());
    }

    // Test constructing a rational

    #[test]
    fn rational_from_different_types() {
        assert_eq!(
            Rational::from(10u8, 5u8).unwrap(),
            Rational { n: 2u8, d: 1u8 }
        );

        assert_eq!(
            Rational::from(32u32, 8u32).unwrap(),
            Rational { n: 4u32, d: 1u32 }
        );

        assert!(Rational::from(77u64, 0u64).is_err());
    }

    // Tests for operator overloads

    #[test]
    fn add_overload() {
        let result = Rational::from(3,17).unwrap() + Rational::from(5,51).unwrap();
        assert_eq!(result, Rational::from(14,51).unwrap());

        let result = Rational::from(3,17).unwrap() + Rational::from(6,51).unwrap();
        assert_eq!(result, Rational::from(5,17).unwrap());
    }


}
