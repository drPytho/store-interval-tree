use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};

/// A utility data structure to represent intervals.
/// It supports open, close and unbounded intervals
///
/// # Examples
/// ```
/// use store_interval_tree::Interval;
/// use std::ops::Bound::*;
///
/// // initialize interval [2,4]
/// let interval1 = Interval::new(2, 4);
///
/// // initialize interval [2,4)
/// let interval2 = Interval::new(2, 4);
///
/// // initialize point [4,4]
/// let point1 = Interval::point(4);
///
/// // compare intervals
/// // first, lower bounds are compared. if they're equal, higher bounds will be compared
/// assert!(interval2 < interval1);
///
/// // check if two intervals overlap
/// assert!(Interval::overlaps(&interval1, &interval2));
///
/// // check if one point and an interval overlap
/// assert!(Interval::overlaps(&interval1, &point1));
/// assert!(!Interval::overlaps(&interval2, &point1));
///
/// // check if one interval contains another interval
/// assert!(Interval::contains(&interval1, &interval2));
///
/// // get overlapped interval between two intervals
/// assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == interval2);
/// ```
#[derive(Clone, Debug, Hash)]
pub struct Interval {
    low: usize,
    high: usize,
}

impl Interval {
    /// Creates a new interval
    ///
    /// # Arguments
    /// * `low`: lower bound of the interval
    /// * `high`: higher bound of the interval
    ///
    /// # Panics
    /// * panics if `low` > `high`. `low` == `high` is acceptable if interval is closed at both sides: [low, high]
    ///
    /// # Example
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // create the interval [2,4)
    /// let interval1 = Interval::new(2, 4);
    ///
    /// // create the interval (-inf,4)
    /// let interval2 = Interval::new(0, 4);
    ///
    ///
    /// // create the interval (1,+inf)
    /// let interval3 = Interval::new(1, usize::MAX);
    /// ```
    #[must_use]
    pub fn new(low: usize, high: usize) -> Interval {
        let interval = Interval { low, high };

        assert!(Interval::valid(&interval), "Interval is not valid");
        interval
    }

    /// Creates a point.
    ///
    /// # Arguments
    /// * `value`: value of the point
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // create point (2) or equivalently interval [2,2]
    /// let point1 = Interval::point(2);
    /// ```
    #[must_use]
    pub fn point(value: usize) -> Interval {
        let low = value;
        let high = value;

        let interval = Interval { low, high };

        assert!(Interval::valid(&interval), "Interval is not valid");

        interval
    }

    /// Creates a duplicate of the interval
    #[must_use]
    pub fn duplicate(&self) -> Interval {
        Interval {
            low: self.get_low(),
            high: self.get_high(),
        }
    }

    fn valid(interval: &Interval) -> bool {
        interval.low <= interval.high
    }

    /// Get reference to lower bound of the interval
    #[must_use]
    pub fn low(&self) -> usize {
        self.low
    }

    /// Get a duplicate of lower bound of the interval
    #[must_use]
    pub fn get_low(&self) -> usize {
        self.low()
    }

    /// Get reference to higher bound of the interval
    #[must_use]
    pub fn high(&self) -> &usize {
        &self.high
    }

    /// Get a duplicate of higher bound of the interval
    #[must_use]
    pub fn get_high(&self) -> usize {
        self.high
    }

    /// Returns true if `first` and `second` intervals overlap, false otherwise
    #[must_use]
    pub fn overlaps(first: &Interval, second: &Interval) -> bool {
        first.low <= second.high && second.low <= first.high
    }

    /// Returns true if `second` is a sub-interval of `first`, false otherwise
    #[must_use]
    pub fn contains(first: &Interval, second: &Interval) -> bool {
        if Interval::overlaps(first, second) {
            let overlap = Interval::get_overlap(first, second).unwrap();

            overlap == *second
        } else {
            false
        }
    }

    /// Get overlapped interval of `first` and `second`, `None` otherwise
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize intervals
    /// let interval1 = Interval::new(2, 4);
    /// let interval2 = Interval::new(2, 4);
    ///
    /// assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == interval2);
    /// ```
    #[must_use]
    pub fn get_overlap(first: &Interval, second: &Interval) -> Option<Interval> {
        let low = first.low.max(second.low);
        let high = first.high.min(second.high);
        let interval = Interval { low, high };
        if !Interval::valid(&interval) {
            return None;
        }

        Some(interval)
    }
}

impl core::fmt::Display for Interval {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[{},{}]", self.low, self.high)
    }
}

impl PartialEq for Interval {
    fn eq(&self, other: &Self) -> bool {
        self.low == other.low && self.high == other.high
    }
}

impl Eq for Interval {}

impl PartialOrd for Interval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // compare low end of the intervals
        Some(self.cmp(other))
    }
}

impl Ord for Interval {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.low < other.low {
            return Ordering::Less;
        }

        if self.low > other.low {
            return Ordering::Greater;
        }

        if self.high < other.high {
            return Ordering::Less;
        }

        if self.high > other.high {
            return Ordering::Greater;
        }

        Ordering::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_valid_1() {
        assert!(Interval::valid(&Interval::new(2, 2)));
        assert!(Interval::valid(&Interval::new(2, 3)));
        assert!(Interval::valid(&Interval::new(2, 3)));
        assert!(Interval::valid(&Interval::new(2, 3)));

        assert!(Interval::valid(&Interval::new(0, 1)));
        assert!(Interval::valid(&Interval::new(2, usize::MAX)));
        assert!(Interval::valid(&Interval::new(0, usize::MAX)));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_1() {
        assert!(!Interval::valid(&Interval::new(2, 1)));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_2() {
        assert!(!Interval::valid(&Interval::new(2, 1)));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_3() {
        assert!(!Interval::valid(&Interval::new(2, 1)));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_4() {
        assert!(!Interval::valid(&Interval::new(2, 1)));
    }

    #[test]
    fn interval_compare_1() {
        let interval1 = Interval::new(2, 3);
        let interval2 = Interval::new(2, 4);

        let interval3 = Interval::new(1, 3);

        let interval5 = Interval::new(0, 3);
        let interval6 = Interval::new(2, usize::MAX);
        let interval7 = Interval::new(0, 3);
        let interval8 = Interval::new(0, usize::MAX);

        assert!(interval1 == interval1);
        assert!(interval1 < interval2);
        assert!(interval2 > interval1);
        assert!(interval2 > interval3);
        assert!(interval5 < interval6);
        assert!(interval7 < interval6);
        assert!(interval5 < interval8);
        assert!(interval6 > interval8);
    }

    #[test]
    fn interval_overlaps_0() {
        let interval1 = Interval::new(5, 8);
        let interval2 = Interval::new(4, 5);

        assert!(Interval::overlaps(&interval2, &interval1));
        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_1() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(2, 4);

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_2() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(2, 3);

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_3() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(1, 3);

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_4() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(3, 4);

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_5() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(0, 0);

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_6() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(4, 5);

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_7() {
        let interval1 = Interval::new(0, 3);
        let interval2 = Interval::new(1, 5);

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_8() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(4, usize::MAX);

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_get_overlap_1() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(2, 4);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(2, 3));
    }

    #[test]
    fn interval_get_overlap_2() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(2, 4);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(2, 3));
    }

    #[test]
    fn interval_get_overlap_3() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(2, 3);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(2, 3));
    }

    #[test]
    fn interval_get_overlap_4() {
        let interval1 = Interval::new(1, 3);
        let interval2 = Interval::new(1, 4);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(1, 3));
    }

    #[test]
    fn interval_get_overlap_5() {
        let interval1 = Interval::new(0, 3);
        let interval2 = Interval::new(1, 2);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(1, 2));
    }

    #[test]
    fn interval_get_overlap_6() {
        let interval1 = Interval::new(0, 3);
        let interval2 = Interval::new(0, 2);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(0, 2));
    }

    #[test]
    fn interval_get_overlap_7() {
        let interval1 = Interval::new(2, 3);
        let interval2 = Interval::new(0, 3);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(2, 3));
    }

    #[test]
    fn interval_get_overlap_8() {
        let interval1 = Interval::new(2, usize::MAX);
        let interval2 = Interval::new(0, usize::MAX);

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(2, usize::MAX)
        );
    }

    #[test]
    fn interval_get_overlap_9() {
        let interval1 = Interval::new(2, 3);
        let interval2 = Interval::new(4, 5);

        assert!(Interval::get_overlap(&interval1, &interval2).is_none());
    }

    #[test]
    fn interval_get_overlap_10() {
        let interval1 = Interval::new(2, 3);
        let interval2 = Interval::new(4, 4);

        assert!(Interval::get_overlap(&interval1, &interval2).is_none());
    }

    #[test]
    fn interval_get_overlap_11() {
        let interval1 = Interval::new(3, 4);
        let interval2 = Interval::new(2, 3);

        assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == Interval::new(3, 3));
    }

    #[test]
    fn interval_contains_1() {
        let interval1 = Interval::new(1, 4);
        let interval2 = Interval::new(2, 3);

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_2() {
        let interval1 = Interval::new(1, 4);
        let interval2 = Interval::new(1, 3);

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_3() {
        let interval1 = Interval::new(1, 4);
        let interval2 = Interval::new(1, 3);

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_4() {
        let interval1 = Interval::new(1, 4);
        let interval2 = Interval::new(2, 4);

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_5() {
        let interval1 = Interval::new(1, 4);
        let interval2 = Interval::new(2, 4);

        assert!(Interval::contains(&interval1, &interval2));
    }
}
