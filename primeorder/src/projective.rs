//! Projective curve points.

#![allow(clippy::needless_range_loop, clippy::op_ref)]

use crate::{AffinePoint, Field, PrimeCurveParams};
use core::{
    borrow::Borrow,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use elliptic_curve::{
    bigint::{ArrayEncoding, Encoding},
    generic_array::ArrayLength,
    group::{
        self,
        cofactor::CofactorGroup,
        prime::{PrimeCurve, PrimeGroup},
        Group, GroupEncoding,
    },
    ops::LinearCombination,
    rand_core::RngCore,
    sec1::{CompressedPoint, ModulusSize, UncompressedPointSize},
    subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption},
    zeroize::DefaultIsZeroes,
    Error, FieldBytes, FieldSize, PublicKey, Result, Scalar,
};

/// Point on a Weierstrass curve in projective coordinates.
#[derive(Clone, Copy, Debug)]
pub struct ProjectivePoint<C: PrimeCurveParams> {
    x: C::FieldElement,
    y: C::FieldElement,
    z: C::FieldElement,
}

impl<C> ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    /// Additive identity of the group a.k.a. the point at infinity.
    pub const IDENTITY: Self = Self {
        x: C::ZERO,
        y: C::ONE,
        z: C::ZERO,
    };

    /// Base point of the curve.
    pub const GENERATOR: Self = Self {
        x: C::GENERATOR.0,
        y: C::GENERATOR.1,
        z: C::ONE,
    };

    /// Returns the affine representation of this point, or `None` if it is the identity.
    pub fn to_affine(&self) -> AffinePoint<C> {
        self.z
            .invert()
            .map(|zinv| AffinePoint {
                x: self.x * &zinv,
                y: self.y * &zinv,
                infinity: 0,
            })
            .unwrap_or(AffinePoint::IDENTITY)
    }

    /// Returns `-self`.
    pub fn neg(&self) -> Self {
        Self {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }

    /// Returns `self + other`.
    pub fn add(&self, other: &Self) -> Self {
        // We implement the complete addition formula from Renes-Costello-Batina 2015
        // (https://eprint.iacr.org/2015/1060 Algorithm 7).
        
        let xx = self.x * &other.x;
        let yy = self.y * &other.y;
        let zz = self.z * &other.z;

        let n_xx_yy = (xx + &yy).neg();
        let n_yy_zz = (yy + &zz).neg();
        let n_xx_zz = (xx + &zz).neg();
        let xy_pairs = ((self.x + &self.y) * &(other.x + &other.y)) + &n_xx_yy;
        let yz_pairs = ((self.y + &self.z) * &(other.y + &other.z)) + &n_yy_zz;
        let xz_pairs = ((self.x + &self.z) * &(other.x + &other.z)) + &n_xx_zz;

        let bzz = C::EQUATION_B * zz;
        let bzz3 = bzz.double() + &bzz;

        let yy_m_bzz3 = yy + &bzz3.neg();
        let yy_p_bzz3 = yy + &bzz3;

        let byz = C::EQUATION_B * &yz_pairs;
        let byz3 = byz.double() + byz;

        let xx3 = xx.double() + &xx;
        let bxx9 = (xx3.double() + &xx3) * C::EQUATION_B;

        let new_x = (xy_pairs * &yy_m_bzz3) + &(byz3 * &xz_pairs).neg(); // m1
        let new_y = (yy_p_bzz3 * &yy_m_bzz3) + &(bxx9 * &xz_pairs);
        let new_z = (yz_pairs * &yy_p_bzz3) + &(xx3 * &xy_pairs);

        ProjectivePoint {
            x: new_x,
            y: new_y,
            z: new_z,
        }
    }

    /// Returns `self + other`.
    fn add_mixed(&self, other: &AffinePoint<C>) -> Self {
        // We implement the complete addition formula from Renes-Costello-Batina 2015
        // (https://eprint.iacr.org/2015/1060 Algorithm 8).

        let xx = self.x * &other.x;
        let yy = self.y * &other.y;
        let xy_pairs = ((self.x + &self.y) * &(other.x + &other.y)) + &(xx + &yy).neg();
        let yz_pairs = (other.y * &self.z) + &self.y;
        let xz_pairs = (other.x * &self.z) + &self.x;

        let bzz = C::EQUATION_B * &self.z;
        let bzz3 = bzz.double() + bzz;

        let yy_m_bzz3 = yy + &bzz3.neg();
        let yy_p_bzz3 = yy + &bzz3;

        let byz = C::EQUATION_B * &yz_pairs;
        let byz3 = byz.double() + byz;

        let xx3 = xx.double() + &xx;
        let bxx9 = C::EQUATION_B * &(xx3.double() + &xx3);

        let mut ret = ProjectivePoint {
            x: ((xy_pairs * &yy_m_bzz3) + &(byz3 * &xz_pairs).neg()),
            y: ((yy_p_bzz3 * &yy_m_bzz3) + &(bxx9 * &xz_pairs)),
            z: ((yz_pairs * &yy_p_bzz3) + &(xx3 * &xy_pairs)),
        };
        ret.conditional_assign(self, other.is_identity());
        ret
    }

    /// Doubles this point.
    pub fn double(&self) -> Self {
        // We implement the complete addition formula from Renes-Costello-Batina 2015
        // (https://eprint.iacr.org/2015/1060 Algorithm 9).

        let t0 = self.y * self.y;
        let z3 = (t0 + t0).double().double();
        let t1 = self.y * self.z;
        let t2 = (self.z * self.z) * (C::EQUATION_B.double() + C::EQUATION_B); // 6, 7
        let x3 = t2 * z3; // 8
        let y3 = t0 + t2; // 9
        let z3 = t1 * z3; //10
        let t1 = t2.double(); // 11
        let t2 = t1 + t2;
        let t0 = t0 - t2;
        let y3 = x3 + (t0 * y3); // 14, 15
        let t1 = self.x * self.y;
        let x3 = (t0 * t1).double();

        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Returns `self - other`.
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    /// Returns `self - other`.
    fn sub_mixed(&self, other: &AffinePoint<C>) -> Self {
        self.add_mixed(&other.neg())
    }

    /// Returns `[k] self`.
    fn mul(&self, k: &Scalar<C>) -> Self {
        let k = Into::<C::UInt>::into(*k).to_le_byte_array();

        let mut pc = [Self::default(); 16];
        pc[0] = Self::IDENTITY;
        pc[1] = *self;

        for i in 2..16 {
            pc[i] = if i % 2 == 0 {
                pc[i / 2].double()
            } else {
                pc[i - 1].add(self)
            };
        }

        let mut q = Self::IDENTITY;
        let mut pos = C::UInt::BIT_SIZE - 4;

        loop {
            let slot = (k[(pos >> 3) as usize] >> (pos & 7)) & 0xf;

            let mut t = ProjectivePoint::IDENTITY;

            for i in 1..16 {
                t.conditional_assign(
                    &pc[i],
                    Choice::from(((slot as usize ^ i).wrapping_sub(1) >> 8) as u8 & 1),
                );
            }

            q = q.add(&t);

            if pos == 0 {
                break;
            }

            q = q.double().double().double().double();
            pos -= 4;
        }

        q
    }
}

impl<C> CofactorGroup for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    type Subgroup = Self;

    fn clear_cofactor(&self) -> Self::Subgroup {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self> {
        CtOption::new(self, 1.into())
    }

    fn is_torsion_free(&self) -> Choice {
        1.into()
    }
}

impl<C> ConditionallySelectable for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: C::FieldElement::conditional_select(&a.x, &b.x, choice),
            y: C::FieldElement::conditional_select(&a.y, &b.y, choice),
            z: C::FieldElement::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl<C> ConstantTimeEq for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn ct_eq(&self, other: &Self) -> Choice {
        self.to_affine().ct_eq(&other.to_affine())
    }
}

impl<C> Default for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl<C> DefaultIsZeroes for ProjectivePoint<C> where C: PrimeCurveParams {}

impl<C> Eq for ProjectivePoint<C> where C: PrimeCurveParams {}

impl<C> From<AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(p: AffinePoint<C>) -> Self {
        let projective = ProjectivePoint {
            x: p.x,
            y: p.y,
            z: C::ONE,
        };
        Self::conditional_select(&projective, &Self::IDENTITY, p.is_identity())
    }
}

impl<C> From<&AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(p: &AffinePoint<C>) -> Self {
        Self::from(*p)
    }
}

impl<C> From<PublicKey<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(public_key: PublicKey<C>) -> ProjectivePoint<C> {
        AffinePoint::from(public_key).into()
    }
}

impl<C> From<&PublicKey<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(public_key: &PublicKey<C>) -> ProjectivePoint<C> {
        AffinePoint::<C>::from(public_key).into()
    }
}

impl<C> Group for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Scalar = Scalar<C>;

    fn random(mut rng: impl RngCore) -> Self {
        Self::GENERATOR * <Scalar<C> as Field>::random(&mut rng)
    }

    fn identity() -> Self {
        Self::IDENTITY
    }

    fn generator() -> Self {
        Self::GENERATOR
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Self::IDENTITY)
    }

    #[must_use]
    fn double(&self) -> Self {
        ProjectivePoint::double(self)
    }
}

impl<C> GroupEncoding for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    type Repr = CompressedPoint<C>;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        <AffinePoint<C> as GroupEncoding>::from_bytes(bytes).map(Into::into)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // No unchecked conversion possible for compressed points
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_affine().to_bytes()
    }
}

impl<C> group::Curve for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type AffineRepr = AffinePoint<C>;

    fn to_affine(&self) -> AffinePoint<C> {
        ProjectivePoint::to_affine(self)
    }
}

impl<C> LinearCombination for ProjectivePoint<C> where C: PrimeCurveParams {}

impl<C> PrimeGroup for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
}

impl<C> PrimeCurve for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    type Affine = AffinePoint<C>;
}

impl<C> PartialEq for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl<C> TryFrom<ProjectivePoint<C>> for PublicKey<C>
where
    C: PrimeCurveParams,
{
    type Error = Error;

    fn try_from(point: ProjectivePoint<C>) -> Result<PublicKey<C>> {
        AffinePoint::<C>::from(point).try_into()
    }
}

impl<C> TryFrom<&ProjectivePoint<C>> for PublicKey<C>
where
    C: PrimeCurveParams,
{
    type Error = Error;

    fn try_from(point: &ProjectivePoint<C>) -> Result<PublicKey<C>> {
        AffinePoint::<C>::from(point).try_into()
    }
}

//
// Arithmetic trait impls
//

impl<C> Add<ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add(&self, &other)
    }
}

impl<C> Add<&ProjectivePoint<C>> for &ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add(self, other)
    }
}

impl<C> Add<&ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add(&self, other)
    }
}

impl<C> AddAssign<ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn add_assign(&mut self, rhs: ProjectivePoint<C>) {
        *self = ProjectivePoint::add(self, &rhs);
    }
}

impl<C> AddAssign<&ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn add_assign(&mut self, rhs: &ProjectivePoint<C>) {
        *self = ProjectivePoint::add(self, rhs);
    }
}

impl<C> Add<AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add_mixed(&self, &other)
    }
}

impl<C> Add<&AffinePoint<C>> for &ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: &AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add_mixed(self, other)
    }
}

impl<C> Add<&AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn add(self, other: &AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::add_mixed(&self, other)
    }
}

impl<C> AddAssign<AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn add_assign(&mut self, rhs: AffinePoint<C>) {
        *self = ProjectivePoint::add_mixed(self, &rhs);
    }
}

impl<C> AddAssign<&AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn add_assign(&mut self, rhs: &AffinePoint<C>) {
        *self = ProjectivePoint::add_mixed(self, rhs);
    }
}

impl<C> Sum for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(ProjectivePoint::IDENTITY, |a, b| a + b)
    }
}

impl<'a, C> Sum<&'a ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sum<I: Iterator<Item = &'a ProjectivePoint<C>>>(iter: I) -> Self {
        iter.cloned().sum()
    }
}

impl<C> Sub<ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub(&self, &other)
    }
}

impl<C> Sub<&ProjectivePoint<C>> for &ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub(self, other)
    }
}

impl<C> Sub<&ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub(&self, other)
    }
}

impl<C> SubAssign<ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sub_assign(&mut self, rhs: ProjectivePoint<C>) {
        *self = ProjectivePoint::sub(self, &rhs);
    }
}

impl<C> SubAssign<&ProjectivePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sub_assign(&mut self, rhs: &ProjectivePoint<C>) {
        *self = ProjectivePoint::sub(self, rhs);
    }
}

impl<C> Sub<AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub_mixed(&self, &other)
    }
}

impl<C> Sub<&AffinePoint<C>> for &ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: &AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub_mixed(self, other)
    }
}

impl<C> Sub<&AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn sub(self, other: &AffinePoint<C>) -> ProjectivePoint<C> {
        ProjectivePoint::sub_mixed(&self, other)
    }
}

impl<C> SubAssign<AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sub_assign(&mut self, rhs: AffinePoint<C>) {
        *self = ProjectivePoint::sub_mixed(self, &rhs);
    }
}

impl<C> SubAssign<&AffinePoint<C>> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    fn sub_assign(&mut self, rhs: &AffinePoint<C>) {
        *self = ProjectivePoint::sub_mixed(self, rhs);
    }
}

impl<C, S> Mul<S> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    S: Borrow<Scalar<C>>,
{
    type Output = Self;

    fn mul(self, scalar: S) -> Self {
        ProjectivePoint::mul(&self, scalar.borrow())
    }
}

impl<C> Mul<&Scalar<C>> for &ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn mul(self, scalar: &Scalar<C>) -> ProjectivePoint<C> {
        ProjectivePoint::mul(self, scalar)
    }
}

impl<C, S> MulAssign<S> for ProjectivePoint<C>
where
    C: PrimeCurveParams,
    S: Borrow<Scalar<C>>,
{
    fn mul_assign(&mut self, scalar: S) {
        *self = ProjectivePoint::mul(self, scalar.borrow());
    }
}

impl<C> Neg for ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn neg(self) -> ProjectivePoint<C> {
        ProjectivePoint::neg(&self)
    }
}

impl<'a, C> Neg for &'a ProjectivePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = ProjectivePoint<C>;

    fn neg(self) -> ProjectivePoint<C> {
        ProjectivePoint::neg(self)
    }
}
