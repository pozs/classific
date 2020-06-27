use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

/// Implementations define a linear ordering over the type `T`, which *can* be semantically
/// different from [`Ord::cmp`].
///
/// By convention, the ordering should fulfill the following properties
/// (for all `a`, `b` and `c`):
/// - connex: `a <= b` or `b <= a`
/// - antisymmetric: if `a <= b` and `b <= a` then `a == b`
/// - transitive: if `a <= b` and `b <= c` then `a <= c`
///
/// (where `a <= b` can be also understood as `!(a > b)`)
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, comparing, natural_order, reverse_order};
///
/// assert_eq!(natural_order().cmp(&1, &2), Ordering::Less);
/// assert_eq!(comparing(|v| v & !3).cmp(&1, &2), Ordering::Equal);
/// assert_eq!(reverse_order().cmp(&1, &2), Ordering::Greater);
/// ```
pub trait Comparator<T: ?Sized> {
    /// This method returns an [`Ordering`] between `left` and `right`.
    ///
    /// By convention, `comparator.cmp(&left, &right)` returns the ordering matching the expression
    /// `left <operator> right` if true.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cmp::Ordering;
    /// use classific::{Comparator, comparing, natural_order, reverse_order};
    ///
    /// assert_eq!(natural_order().cmp(&1, &2), Ordering::Less);
    /// assert_eq!(comparing(|v| v & !3).cmp(&1, &2), Ordering::Equal);
    /// assert_eq!(reverse_order().cmp(&1, &2), Ordering::Greater);
    /// ```
    fn cmp(&self, left: &T, right: &T) -> Ordering;

    /// This method returns a [`Comparator`] which is semantically reversed from `self`.
    ///
    /// The ordering of the result [`Comparator`] will fulfill the following
    /// (for all `a`, `b`):
    /// ```
    /// use classific::Comparator;
    ///
    /// fn test<T>(a: &T, b: &T, comparator: impl Comparator<T>) {
    ///     assert_eq!(comparator.cmp(a, b).reverse(), comparator.reversed().cmp(a, b));
    /// }
    /// ```
    fn reversed(self) -> ReversedOrder<T, Self>
    where
        Self: Sized,
    {
        ReversedOrder(self, PhantomData)
    }

    /// This method returns a [`Comparator`] which is further refining the semantics of `self`.
    ///
    /// [`next::cmp`](Comparator::cmp) is called only when [`self::cmp`](Comparator::cmp)
    /// returns [`Ordering::Equal`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cmp::Ordering;
    /// use classific::{Comparator, comparing, natural_order, reverse_order};
    ///
    /// assert_eq!(comparing(|t: &(i8, i8)| t.0).then(comparing(|t: &(i8, i8)| t.1)).cmp(&(1, 2), &(1, 3)), Ordering::Less);
    /// ```
    fn then<N>(self, next: N) -> CompareThen<T, Self, N>
    where
        Self: Sized,
        N: Comparator<T>,
    {
        CompareThen(self, next, PhantomData)
    }

    /// This function returns the greater instace (out of `left` and `right`)
    /// according to [`cmp`](Comparator).
    ///
    /// # Examples
    ///
    /// ```
    /// use classific::{Comparator, reverse_order};
    ///
    /// assert_eq!(reverse_order().max(&1, &2), &1);
    /// ```
    fn max<'a>(&self, left: &'a T, right: &'a T) -> &'a T {
        match self.cmp(left, right) {
            Ordering::Less => right,
            _ => left,
        }
    }

    /// This function returns the less instace (out of `left` and `right`)
    /// according to [`cmp`](Comparator).
    ///
    /// # Examples
    ///
    /// ```
    /// use classific::{Comparator, reverse_order};
    ///
    /// assert_eq!(reverse_order().min(&1, &2), &2);
    /// ```
    fn min<'a>(&self, left: &'a T, right: &'a T) -> &'a T {
        match self.cmp(left, right) {
            Ordering::Greater => right,
            _ => left,
        }
    }
}

/// This function returns a [`Comparator`] for `T` which follows
/// the semantics of [`Ord::cmp`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, natural_order};
///
/// assert_eq!(natural_order().cmp(&1, &2), Ordering::Less);
/// assert_eq!(natural_order().cmp(&2, &2), Ordering::Equal);
/// assert_eq!(natural_order().cmp(&3, &2), Ordering::Greater);
/// ```
pub fn natural_order<T>() -> NaturalOrder<T>
where
    T: ?Sized + Ord,
{
    NaturalOrder(PhantomData)
}

/// This function returns a [`Comparator`] for `T` which follows
/// the reverse semantics of [`Ord::cmp`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, reverse_order};
///
/// assert_eq!(reverse_order().cmp(&3, &2), Ordering::Less);
/// assert_eq!(reverse_order().cmp(&2, &2), Ordering::Equal);
/// assert_eq!(reverse_order().cmp(&1, &2), Ordering::Greater);
/// ```
pub fn reverse_order<T>() -> ReversedNaturalOrder<T>
where
    T: ?Sized + Ord,
{
    ReversedNaturalOrder(PhantomData)
}

/// This function returns a [`Comparator`] for `S` which first maps values to `T`
/// then compare them with [`Ord::cmp`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, comparing};
///
/// assert_eq!(comparing(|t: &(i8, i8)| t.1).cmp(&(3, 1), &(2, 2)), Ordering::Less);
/// ```
pub fn comparing<S, T, F>(map: F) -> Comparing<S, T, F>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> T,
{
    Comparing(map, PhantomData, PhantomData)
}

/// This function returns a [`Comparator`] for `S` which first maps values to `&T`
/// then compare them with [`Ord::cmp`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, comparing_ref};
///
/// assert_eq!(comparing_ref(|t: &(i8, i8)| &t.1).cmp(&(3, 1), &(2, 2)), Ordering::Less);
/// ```
pub fn comparing_ref<S, T, F>(map: F) -> ComparingRef<S, T, F>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> &T,
{
    ComparingRef(map, PhantomData, PhantomData)
}

/// This function returns a [`Comparator`] for `S` which first maps values to `T`
/// then compare them with [`cmp`](Comparator).
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, comparing_with, reverse_order};
///
/// assert_eq!(comparing_with(|t: &(i8, i8)| t.1, reverse_order()).cmp(&(3, 1), &(2, 2)), Ordering::Greater);
/// ```
pub fn comparing_with<S, T, F, C>(map: F, cmp: C) -> ComparingWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> T,
    C: Comparator<T>,
{
    ComparingWith(map, cmp, PhantomData, PhantomData)
}

/// This function returns a [`Comparator`] for `S` which first maps values to `&T`
/// then compare them with [`cmp`](Comparator).
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, comparing_ref_with, reverse_order};
///
/// assert_eq!(comparing_ref_with(|t: &(i8, i8)| &t.1, reverse_order()).cmp(&(3, 1), &(2, 2)), Ordering::Greater);
/// ```
pub fn comparing_ref_with<S, T, F, C>(map: F, cmp: C) -> ComparingRefWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> &T,
    C: Comparator<T>,
{
    ComparingRefWith(map, cmp, PhantomData, PhantomData)
}

/// This function returns a [`Comparator`] for `T` which follows the semantics of
/// [`PartialOrd::partial_cmp`] but when that returns [`None`](Option::None) it calls
/// the underlying [`Comparator`] `cmp`.
///
/// See [`at_least`] and [`at_greatest`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, at_least, partial_order_or};
///
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&f64::NAN, &1_f64), Ordering::Less);
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&f64::NAN, &f64::NAN), Ordering::Equal);
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&1_f64, &f64::NAN), Ordering::Greater);
/// ```
pub fn partial_order_or<T, C>(cmp: C) -> PartialOrderOr<T, C>
where
    T: ?Sized + PartialOrd<T>,
    C: Comparator<T>,
{
    PartialOrderOr(cmp, PhantomData)
}

/// This function returns a [`Comparator`] for `T` which divides `T` instances into 2 categories.
///
/// - the ones for which `is_at_least` returns `true`:
///   these are considered [`Ordering::Less`] than the other category,
///   and [`Ordering::Equal`] to each other
/// - and the ones for which `is_at_least` returns `false`:
///   these are considered [`Ordering::Greater`] than the other category,
///   and [`Ordering::Equal`] to each other
///
/// See [`at_greatest`] and [`partial_order_or`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, at_least, partial_order_or};
///
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&f64::NAN, &1_f64), Ordering::Less);
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&f64::NAN, &f64::NAN), Ordering::Equal);
/// assert_eq!(partial_order_or(at_least(|f: &f64| f.is_nan())).cmp(&1_f64, &f64::NAN), Ordering::Greater);
/// ```
pub fn at_least<T, F>(is_at_least: F) -> AtLeast<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    AtLeast(is_at_least, PhantomData)
}

/// This function returns a [`Comparator`] for `T` which divides `T` instances into 2 categories.
///
/// - the ones for which `is_at_least` returns `true`:
///   these are considered [`Ordering::Less`] than the other category,
///   and [`Ordering::Equal`] to each other
/// - and the ones for which `is_at_least` returns `false`:
///   these are considered [`Ordering::Greater`] than the other category,
///   and [`Ordering::Equal`] to each other
///
/// See [`at_least`] and [`partial_order_or`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, at_greatest, partial_order_or};
///
/// assert_eq!(partial_order_or(at_greatest(|f: &f64| f.is_nan())).cmp(&f64::NAN, &1_f64), Ordering::Greater);
/// assert_eq!(partial_order_or(at_greatest(|f: &f64| f.is_nan())).cmp(&f64::NAN, &f64::NAN), Ordering::Equal);
/// assert_eq!(partial_order_or(at_greatest(|f: &f64| f.is_nan())).cmp(&1_f64, &f64::NAN), Ordering::Less);
/// ```
pub fn at_greatest<T, F>(is_at_greatest: F) -> AtGreatest<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    AtGreatest(is_at_greatest, PhantomData)
}

/// This function moves a [`Comparator`] into a [`Fn(&T, &T) -> Ordering`](Fn)
/// to make it usable for APIs which doesn't know about [`Comparator`]s.
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
/// use classific::{Comparator, reverse_order, move_to_cmp_fn};
///
/// let slice = &mut [1, 2];
/// slice.sort_by(move_to_cmp_fn(reverse_order()));
/// assert_eq!(slice, &[2, 1]);
/// ```
pub fn move_to_cmp_fn<T>(comparator: impl Comparator<T>) -> impl Fn(&T, &T) -> Ordering
where
    T: ?Sized,
{
    move |left, right| comparator.cmp(left, right)
}

impl<T, F> Comparator<T> for F
where
    T: ?Sized,
    F: Fn(&T, &T) -> Ordering,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        self(left, right)
    }
}

/// See [`natural_order`].
#[derive(Copy, Clone, Debug)]
pub struct NaturalOrder<T: ?Sized + Ord>(PhantomData<*const T>);

impl<T> Comparator<T> for NaturalOrder<T>
where
    T: ?Sized + Ord,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        left.cmp(right)
    }
}

/// See [`reverse_order`].
#[derive(Copy, Clone, Debug)]
pub struct ReversedNaturalOrder<T: ?Sized + Ord>(PhantomData<*const T>);

impl<T> Comparator<T> for ReversedNaturalOrder<T>
where
    T: ?Sized + Ord,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        right.cmp(left)
    }
}

/// See [`Comparator::reversed`].
#[derive(Copy, Clone, Debug)]
pub struct ReversedOrder<T: ?Sized, C: Comparator<T>>(C, PhantomData<*const T>);

impl<T, C> Comparator<T> for ReversedOrder<T, C>
where
    T: ?Sized,
    C: Comparator<T>,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        self.0.cmp(right, left)
    }
}

/// See [`comparing`].
#[derive(Copy, Clone, Debug)]
pub struct Comparing<S: ?Sized, T: ?Sized + Ord, F: Fn(&S) -> T>(
    F,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F> Comparator<S> for Comparing<S, T, F>
where
    S: ?Sized,
    T: Ord,
    F: Fn(&S) -> T,
{
    fn cmp(&self, left: &S, right: &S) -> Ordering {
        Ord::cmp(&self.0(left), &self.0(right))
    }
}

/// See [`comparing_ref`].
#[derive(Copy, Clone, Debug)]
pub struct ComparingRef<S: ?Sized, T: ?Sized + Ord, F: Fn(&S) -> &T>(
    F,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F> Comparator<S> for ComparingRef<S, T, F>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> &T,
{
    fn cmp(&self, left: &S, right: &S) -> Ordering {
        Ord::cmp(self.0(left), self.0(right))
    }
}

/// See [`comparing_with`].
#[derive(Copy, Clone, Debug)]
pub struct ComparingWith<S: ?Sized, T: ?Sized + Ord, F: Fn(&S) -> T, C: Comparator<T>>(
    F,
    C,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F, C> Comparator<S> for ComparingWith<S, T, F, C>
where
    S: ?Sized,
    T: Ord,
    F: Fn(&S) -> T,
    C: Comparator<T>,
{
    fn cmp(&self, left: &S, right: &S) -> Ordering {
        self.1.cmp(&self.0(left), &self.0(right))
    }
}

/// See [`comparing_ref_with`].
#[derive(Copy, Clone, Debug)]
pub struct ComparingRefWith<S: ?Sized, T: ?Sized + Ord, F: Fn(&S) -> &T, C: Comparator<T>>(
    F,
    C,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F, C> Comparator<S> for ComparingRefWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + Ord,
    F: Fn(&S) -> &T,
    C: Comparator<T>,
{
    fn cmp(&self, left: &S, right: &S) -> Ordering {
        self.1.cmp(self.0(left), self.0(right))
    }
}

/// See [`partial_order_or`].
#[derive(Copy, Clone, Debug)]
pub struct PartialOrderOr<T: ?Sized + PartialOrd<T>, C: Comparator<T>>(C, PhantomData<*const T>);

impl<T, C> Comparator<T> for PartialOrderOr<T, C>
where
    T: ?Sized + PartialOrd<T>,
    C: Comparator<T>,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        match left.partial_cmp(right) {
            Some(ord) => ord,
            None => self.0.cmp(left, right),
        }
    }
}

/// See [`at_least`].
#[derive(Copy, Clone, Debug)]
pub struct AtLeast<T: ?Sized, F: Fn(&T) -> bool>(F, PhantomData<*const T>);

impl<T, F> Comparator<T> for AtLeast<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        match (self.0(left), self.0(right)) {
            (a, b) if a == b => Ordering::Equal,
            (true, _) => Ordering::Less,
            _ => Ordering::Greater,
        }
    }
}

/// See [`at_greatest`].
#[derive(Copy, Clone, Debug)]
pub struct AtGreatest<T: ?Sized, F: Fn(&T) -> bool>(F, PhantomData<*const T>);

impl<T, F> Comparator<T> for AtGreatest<T, F>
where
    T: ?Sized,
    F: Fn(&T) -> bool,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        match (self.0(left), self.0(right)) {
            (a, b) if a == b => Ordering::Equal,
            (true, _) => Ordering::Greater,
            _ => Ordering::Less,
        }
    }
}

/// See [`Comparator::then`].
#[derive(Copy, Clone, Debug)]
pub struct CompareThen<T: ?Sized, C: Comparator<T>, N: Comparator<T>>(C, N, PhantomData<*const T>);

impl<T, C, N> Comparator<T> for CompareThen<T, C, N>
where
    T: ?Sized,
    C: Comparator<T>,
    N: Comparator<T>,
{
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        match self.0.cmp(left, right) {
            Ordering::Equal => self.1.cmp(left, right),
            ordering => ordering,
        }
    }
}

/// Implementations define an equivalence class over the type `T`, which *can* be semantically
/// different from [`PartialEq::eq`].
///
/// By convention, the equivalence class should fulfill the following properties
/// (for all `a`, `b` and `c`):
/// - reflexive: `a == a`
/// - symmetric: if `a == b` then `b == a`
/// - transitive: if `a == b` and `b == c` then `a == c`
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by};
///
/// assert!(eq_by(|t: &(i8, i8)| t.1).eq(&(1, 2), &(2, 2)));
/// ```
pub trait EqClass<T: ?Sized> {
    /// This method tests for `left` and `right` values to be equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use classific::{EqClass, natural_eq};
    ///
    /// assert!(natural_eq().eq(&1, &1));
    /// ```
    fn eq(&self, left: &T, right: &T) -> bool;

    /// This method returns an [`EqClass`] which is further refining the semantics of `self`.
    ///
    /// Both [`self::eq`](EqClass::eq) and [`next::eq`](EqClass::eq) is called
    /// and the result is `true` if and only if both returned `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use classific::{EqClass, eq_by};
    ///
    /// assert!(eq_by(|t: &(i8, i8, i8)| t.0).and(eq_by(|t: &(i8, i8, i8)| t.1)).eq(&(1, 2, 3), &(1, 2, 1)));
    /// ```
    fn and<N>(self, next: N) -> BothEq<T, Self, N>
    where
        Self: Sized,
        N: EqClass<T>,
    {
        BothEq(self, next, PhantomData)
    }
}

/// This function returns an [`EqClass`] for `T` which follows
/// the semantics of [`PartialEq::eq`].
///
/// # Examples
///
/// ```
/// use classific::{EqClass, natural_eq};
///
/// assert!(natural_eq().eq(&1, &1));
/// ```
pub fn natural_eq<T>() -> NaturalEq<T>
where
    T: ?Sized + PartialEq<T>,
{
    NaturalEq(PhantomData)
}

/// This function returns an [`EqClass`] for `T` which considers every instance to be equal to every
/// other instace where the instances do not equal to themselves by [`PartialEq::eq`]; otherwise
/// [`PartialEq::eq`] is followed.
///
/// # Examples
///
/// ```
/// use classific::{EqClass, partial_eq};
///
/// assert!(partial_eq().eq(&f64::NAN, &f64::NAN));
/// ```
pub fn partial_eq<T>() -> PartialEqClass<T>
where
    T: ?Sized + PartialEq<T>,
{
    PartialEqClass(PhantomData)
}

/// This function returns an [`EqClass`] for `S` which first maps values to `T`
/// then compare them with [`PartialEq::eq`].
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by};
///
/// assert!(eq_by(|t: &(i8, i8)| t.1).eq(&(1, 2), &(3, 2)));
/// ```
pub fn eq_by<S, T, F>(map: F) -> EqBy<S, T, F>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> T,
{
    EqBy(map, PhantomData, PhantomData)
}

/// This function returns an [`EqClass`] for `S` which first maps values to `&T`
/// then compare them with [`PartialEq::eq`].
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by_ref};
///
/// assert!(eq_by_ref(|t: &(i8, &'static str)| &t.1).eq(&(1, "2"), &(3, "2")));
/// ```
pub fn eq_by_ref<S, T, F>(map: F) -> EqByRef<S, T, F>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> &T,
{
    EqByRef(map, PhantomData, PhantomData)
}

/// This function returns an [`EqClass`] for `S` which first maps values to `T`
/// then compare them with [`PartialEq::eq`].
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by};
///
/// assert!(eq_by(|t: &(i8, i8)| t.1).eq(&(1, 2), &(3, 2)));
/// ```
pub fn eq_by_with<S, T, F, C>(map: F, eq: C) -> EqByWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> T,
    C: EqClass<T>,
{
    EqByWith(map, eq, PhantomData, PhantomData)
}

/// This function returns an [`EqClass`] for `S` which first maps values to `&T`
/// then compare them with [`PartialEq::eq`].
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by_ref};
///
/// assert!(eq_by_ref(|t: &(i8, &'static str)| &t.1).eq(&(1, "2"), &(3, "2")));
/// ```
pub fn eq_by_ref_with<S, T, F, C>(map: F, eq: C) -> EqByRefWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> &T,
    C: EqClass<T>,
{
    EqByRefWith(map, eq, PhantomData, PhantomData)
}

/// This function returns an [`EqClass`] for `T` which considers instances equal
/// if and only if their [hash](Hash) is equal.
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by_hash};
///
/// assert!(eq_by_hash().eq(&1, &1));
/// ```
pub fn eq_by_hash<T>() -> EqByHash<T>
where
    T: ?Sized + Hash,
{
    EqByHash(PhantomData)
}

/// This function returns an [`EqClass`] for `T` which considers instances equal
/// if and only the embedded [`Comparator`] returns [`Ordering::Equal`] for them.
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by_cmp, comparing};
///
/// assert!(eq_by_cmp(comparing(|s: &str| s.to_ascii_uppercase())).eq("Foo", "FOO"));
/// ```
pub fn eq_by_cmp<T, C>(cmp: C) -> EqByCmp<T, C>
where
    T: ?Sized,
    C: Comparator<T>,
{
    EqByCmp(cmp, PhantomData)
}

/// This function moves an [`EqClass`] into a [`Fn(&T, &T) -> bool`](Fn)
/// to make it usable for APIs which doesn't know about [`EqClass`]es.
///
/// # Examples
///
/// ```
/// use classific::{EqClass, eq_by, move_to_eq_fn};
///
/// let mut iter = [(1, 1), (2, 1), (3, 1)].iter();
/// let first = iter.next();
/// let eq = move_to_eq_fn(eq_by(|i: &(i8, i8)| i.1));
/// let r = iter.fold(first, move |acc, next| match acc {
///     Some(a) => if eq(a, next) { Some(next) } else { None },
///     none => none,
/// });
/// assert!(r.is_some());
/// ```
pub fn move_to_eq_fn<T>(eq_class: impl EqClass<T>) -> impl Fn(&T, &T) -> bool
where
    T: ?Sized,
{
    move |left, right| eq_class.eq(left, right)
}

impl<T, F> EqClass<T> for F
where
    T: ?Sized,
    F: Fn(&T, &T) -> bool,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        self(left, right)
    }
}

/// See [`natural_eq`].
#[derive(Copy, Clone, Debug)]
pub struct NaturalEq<T: ?Sized + PartialEq<T>>(PhantomData<*const T>);

impl<T> EqClass<T> for NaturalEq<T>
where
    T: ?Sized + PartialEq<T>,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        left.eq(right)
    }
}

/// See [`partial_eq`].
#[derive(Copy, Clone, Debug)]
pub struct PartialEqClass<T: ?Sized + PartialEq<T>>(PhantomData<*const T>);

impl<T> EqClass<T> for PartialEqClass<T>
where
    T: ?Sized + PartialEq<T>,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        match (left.eq(left), right.eq(right)) {
            (false, false) => true,
            (true, true) => left.eq(right),
            _ => false,
        }
    }
}

/// See [`eq_by`].
#[derive(Copy, Clone, Debug)]
pub struct EqBy<S: ?Sized, T: ?Sized + PartialEq<T>, F: Fn(&S) -> T>(
    F,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F> EqClass<S> for EqBy<S, T, F>
where
    S: ?Sized,
    T: PartialEq<T>,
    F: Fn(&S) -> T,
{
    fn eq(&self, left: &S, right: &S) -> bool {
        self.0(left).eq(&self.0(right))
    }
}

/// See [`eq_by_ref`].
#[derive(Copy, Clone, Debug)]
pub struct EqByRef<S: ?Sized, T: ?Sized + PartialEq<T>, F: Fn(&S) -> &T>(
    F,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F> EqClass<S> for EqByRef<S, T, F>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> &T,
{
    fn eq(&self, left: &S, right: &S) -> bool {
        self.0(left).eq(self.0(right))
    }
}

/// See [`eq_by_with`].
#[derive(Copy, Clone, Debug)]
pub struct EqByWith<S: ?Sized, T: ?Sized + PartialEq<T>, F: Fn(&S) -> T, C: EqClass<T>>(
    F,
    C,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F, C> EqClass<S> for EqByWith<S, T, F, C>
where
    S: ?Sized,
    T: PartialEq<T>,
    F: Fn(&S) -> T,
    C: EqClass<T>,
{
    fn eq(&self, left: &S, right: &S) -> bool {
        self.1.eq(&self.0(left), &self.0(right))
    }
}

/// See [`eq_by_ref_with`].
#[derive(Copy, Clone, Debug)]
pub struct EqByRefWith<S: ?Sized, T: ?Sized + PartialEq<T>, F: Fn(&S) -> &T, C: EqClass<T>>(
    F,
    C,
    PhantomData<*const S>,
    PhantomData<*const T>,
);

impl<S, T, F, C> EqClass<S> for EqByRefWith<S, T, F, C>
where
    S: ?Sized,
    T: ?Sized + PartialEq<T>,
    F: Fn(&S) -> &T,
    C: EqClass<T>,
{
    fn eq(&self, left: &S, right: &S) -> bool {
        self.1.eq(self.0(left), self.0(right))
    }
}

/// See [`eq_by_hash`].
#[derive(Copy, Clone, Debug)]
pub struct EqByHash<T: ?Sized + Hash>(PhantomData<*const T>);

impl<T> EqClass<T> for EqByHash<T>
where
    T: ?Sized + Hash,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        #[inline]
        fn hash<T: ?Sized + Hash>(to_hash: &T) -> u64 {
            let mut hasher = DefaultHasher::new();
            to_hash.hash(&mut hasher);
            hasher.finish()
        }

        hash(left) == hash(right)
    }
}

/// See [`eq_by_cmp`].
#[derive(Copy, Clone, Debug)]
pub struct EqByCmp<T: ?Sized, C: Comparator<T>>(C, PhantomData<*const T>);

impl<T, C> EqClass<T> for EqByCmp<T, C>
where
    T: ?Sized,
    C: Comparator<T>,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        Ordering::Equal == self.0.cmp(left, right)
    }
}

/// See [`EqClass::and`].
#[derive(Copy, Clone, Debug)]
pub struct BothEq<T: ?Sized, C: EqClass<T>, N: EqClass<T>>(C, N, PhantomData<*const T>);

impl<T, C, N> EqClass<T> for BothEq<T, C, N>
where
    T: ?Sized,
    C: EqClass<T>,
    N: EqClass<T>,
{
    fn eq(&self, left: &T, right: &T) -> bool {
        self.0.eq(left, right) && self.1.eq(left, right)
    }
}

mod tests;
