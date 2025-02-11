use core::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    ops::Bound::{self, Excluded, Included, Unbounded},
};
use std::string::{String, ToString};

/// A utility data structure to represent intervals.
/// It supports open, close and unbounded intervals
///
/// # Examples
/// ```
/// use store_interval_tree::Interval;
/// use std::ops::Bound::*;
///
/// // initialize interval [2,4]
/// let interval1 = Interval::new(Included(2), Included(4));
///
/// // initialize interval [2,4)
/// let interval2 = Interval::new(Included(2), Excluded(4));
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
    low: Bound<usize>,
    high: Bound<usize>,
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
    /// let interval1 = Interval::new(Included(2), Excluded(4));
    ///
    /// // create the interval (-inf,4)
    /// let interval2 = Interval::new(Unbounded, Excluded(4));
    ///
    ///
    /// // create the interval (1,+inf)
    /// let interval3 = Interval::new(Excluded(1), Unbounded);
    /// ```
    #[must_use]
    pub fn new(low: Bound<usize>, high: Bound<usize>) -> Interval {
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
        let low = Included(value);
        let high = low;

        let interval = Interval { low, high };

        assert!(Interval::valid(&interval), "Interval is not valid");

        interval
    }

    /// Creates a duplicate of the interval
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let interval = Interval::new(Included(2), Unbounded);
    /// let duplicate = interval.duplicate();
    ///
    /// assert!(interval == duplicate);
    /// ```
    #[must_use]
    pub fn duplicate(&self) -> Interval {
        Interval {
            low: self.get_low(),
            high: self.get_high(),
        }
    }

    fn valid(interval: &Interval) -> bool {
        match (&interval.low(), &interval.high()) {
            (Included(low), Included(high)) => low <= high,

            (Included(low) | Excluded(low), Excluded(high)) | (Excluded(low), Included(high)) => {
                low < high
            }

            _ => true,
        }
    }

    /// Get reference to lower bound of the interval
    #[must_use]
    pub fn low(&self) -> &Bound<usize> {
        &self.low
    }

    /// Get a duplicate of lower bound of the interval
    #[must_use]
    pub fn get_low(&self) -> Bound<usize> {
        self.low
    }

    /// Get reference to higher bound of the interval
    #[must_use]
    pub fn high(&self) -> &Bound<usize> {
        &self.high
    }

    /// Get a duplicate of higher bound of the interval
    #[must_use]
    pub fn get_high(&self) -> Bound<usize> {
        self.high
    }

    /// Returns true if `first` and `second` intervals overlap, false otherwise
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let interval1 = Interval::new(Included(2), Included(4));
    /// let interval2 = Interval::new(Included(2), Excluded(4));
    /// let point1 = Interval::point(4);
    ///
    /// assert!(Interval::overlaps(&interval1, &interval2));
    /// assert!(Interval::overlaps(&interval1, &point1));
    /// assert!(!Interval::overlaps(&interval2, &point1));
    /// ```
    #[must_use]
    pub fn overlaps(first: &Interval, second: &Interval) -> bool {
        let high: &Bound<usize>;
        let low: &Bound<usize>;

        if *first == *second {
            return true;
        } else if first < second {
            low = second.low();
            high = first.high();
        } else {
            low = first.low();
            high = second.high();
        }

        match (low, high) {
            (Included(low), Included(high)) => high >= low,
            (Included(low) | Excluded(low), Excluded(high)) | (Excluded(low), Included(high)) => {
                high > low
            }
            _ => true,
        }
    }

    /// Returns true if `second` is a sub-interval of `first`, false otherwise
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let interval1 = Interval::new(Included(2), Included(4));
    /// let interval2 = Interval::new(Included(2), Excluded(4));
    ///
    /// assert!(Interval::contains(&interval1, &interval2));
    /// ```
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
    /// let interval1 = Interval::new(Included(2), Included(4));
    /// let interval2 = Interval::new(Included(2), Excluded(4));
    ///
    /// assert!(Interval::get_overlap(&interval1, &interval2).unwrap() == interval2);
    /// ```
    #[must_use]
    pub fn get_overlap(first: &Interval, second: &Interval) -> Option<Interval> {
        if !Interval::overlaps(first, second) {
            return None;
        }

        let low = match (first.low(), second.low()) {
            (Included(low1) | Excluded(low1), Included(low2))
            | (Excluded(low1), Excluded(low2)) => {
                if low1 >= low2 {
                    first.low
                } else {
                    second.low
                }
            }
            (Included(low1), Excluded(low2)) => {
                if low1 > low2 {
                    first.low
                } else {
                    second.low
                }
            }
            (Unbounded, Included(_) | Excluded(_)) => second.low,
            (Included(_) | Excluded(_), Unbounded) => first.low,

            (Unbounded, Unbounded) => Unbounded,
        };

        let high = match (first.high(), second.high()) {
            (Included(high1) | Excluded(high1), Included(high2))
            | (Excluded(high1), Excluded(high2)) => {
                if high1 <= high2 {
                    first.high
                } else {
                    second.high
                }
            }
            (Included(high1), Excluded(high2)) => {
                if high1 < high2 {
                    first.high
                } else {
                    second.high
                }
            }
            (Unbounded, Included(_) | Excluded(_)) => second.high,
            (Included(_) | Excluded(_), Unbounded) => first.high,

            (Unbounded, Unbounded) => Unbounded,
        };

        Some(Interval { low, high })
    }

    /// Returns the span between the start and the end of the interval.
    /// None if the interval is unbounded.
    #[must_use]
    pub fn span(&self) -> Option<usize> {
        match (&self.low(), &self.high()) {
            (Included(low), Included(high)) => Some(*high + 1 - *low),
            (Included(low), Excluded(high)) | (Excluded(low), Included(high)) => Some(*high - *low),
            (Excluded(low), Excluded(high)) => Some(*high - 1 - *low),
            _ => None,
        }
    }
}

impl core::fmt::Display for Interval {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let low = match &self.low() {
            Included(low) => format!("[{}", low),
            Excluded(low) => format!("({}", low),
            Unbounded => "(_".to_string(),
        };

        let high: String = match &self.high() {
            Included(high) => format!("{}]", high),
            Excluded(high) => format!("{})", high),
            Unbounded => "_)".to_string(),
        };

        write!(f, "{},{}", low, high)
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
        let mut result = match (&self.low(), &other.low()) {
            (Included(low1), Included(low2)) | (Excluded(low1), Excluded(low2)) => {
                if low1 < low2 {
                    Some(Ordering::Less)
                } else if low1 == low2 {
                    None
                } else {
                    Some(Ordering::Greater)
                }
            }
            (Included(low1), Excluded(low2)) => {
                if low1 <= low2 {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }
            (Excluded(low1), Included(low2)) => {
                if low1 < low2 {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }

            (Unbounded, Included(_) | Excluded(_)) => Some(Ordering::Less),

            (Included(_) | Excluded(_), Unbounded) => Some(Ordering::Greater),

            (Unbounded, Unbounded) => None,
        };

        // if low end was not enough to determine ordering, use high end
        if result.is_none() {
            result = match (&self.high(), &other.high()) {
                (Included(high1), Included(high2)) | (Excluded(high1), Excluded(high2)) => {
                    if high1 < high2 {
                        Some(Ordering::Less)
                    } else if high1 == high2 {
                        Some(Ordering::Equal)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
                (Included(high1), Excluded(high2)) => {
                    if high1 < high2 {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
                (Excluded(high1), Included(high2)) => {
                    if high1 <= high2 {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                }
                (Unbounded, Included(_) | Excluded(_)) => Some(Ordering::Greater),

                (Included(_) | Excluded(_), Unbounded) => Some(Ordering::Less),

                (Unbounded, Unbounded) => Some(Ordering::Equal),
            };
        }

        result
    }
}

impl Ord for Interval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_valid_1() {
        assert!(Interval::valid(&Interval::new(Included(2), Included(2))));
        assert!(Interval::valid(&Interval::new(Excluded(2), Included(3))));
        assert!(Interval::valid(&Interval::new(Included(2), Excluded(3))));
        assert!(Interval::valid(&Interval::new(Excluded(2), Excluded(3))));

        assert!(Interval::valid(&Interval::new(Unbounded, Included(1))));
        assert!(Interval::valid(&Interval::new(Excluded(2), Unbounded)));
        assert!(Interval::valid(&Interval::new(Unbounded, Unbounded)));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_1() {
        assert!(!Interval::valid(&Interval::new(Included(2), Included(1))));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_2() {
        assert!(!Interval::valid(&Interval::new(Excluded(2), Included(1))));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_3() {
        assert!(!Interval::valid(&Interval::new(Included(2), Excluded(1))));
    }

    #[test]
    #[should_panic(expected = "Interval is not valid")]
    fn interval_panic_new_4() {
        assert!(!Interval::valid(&Interval::new(Excluded(2), Excluded(1))));
    }

    #[test]
    fn interval_compare_1() {
        let interval1 = Interval::new(Included(2), Included(3));
        let interval2 = Interval::new(Included(2), Excluded(3));
        let interval3 = Interval::new(Excluded(2), Included(3));
        let interval4 = Interval::new(Excluded(2), Excluded(3));

        let interval5 = Interval::new(Unbounded, Excluded(3));
        let interval6 = Interval::new(Excluded(2), Unbounded);
        let interval7 = Interval::new(Unbounded, Excluded(3));
        let interval8 = Interval::new(Unbounded, Unbounded);

        assert!(interval1 == interval1);
        assert!(interval1 > interval2);
        assert!(interval2 < interval1);
        assert!(interval2 < interval3);
        assert!(interval3 > interval4);
        assert!(interval5 < interval6);
        assert!(interval7 < interval6);
        assert!(interval5 < interval8);
        assert!(interval6 > interval8);
    }

    #[test]
    fn interval_overlaps_1() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Included(2), Included(4));

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_2() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Included(2), Excluded(3));

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_3() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Excluded(1), Excluded(3));

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_4() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Excluded(3), Excluded(4));

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_5() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Excluded(0), Excluded(1));

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_6() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Excluded(4), Excluded(5));

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_7() {
        let interval1 = Interval::new(Unbounded, Included(3));
        let interval2 = Interval::new(Excluded(1), Excluded(5));

        assert!(Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_overlaps_8() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Excluded(4), Unbounded);

        assert!(!Interval::overlaps(&interval1, &interval2));
    }

    #[test]
    fn interval_get_overlap_1() {
        let interval1 = Interval::new(Included(1), Included(3));
        let interval2 = Interval::new(Included(2), Included(4));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Included(2), Included(3))
        );
    }

    #[test]
    fn interval_get_overlap_2() {
        let interval1 = Interval::new(Included(1), Excluded(3));
        let interval2 = Interval::new(Included(2), Included(4));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Included(2), Excluded(3))
        );
    }

    #[test]
    fn interval_get_overlap_3() {
        let interval1 = Interval::new(Included(1), Excluded(3));
        let interval2 = Interval::new(Included(2), Included(3));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Included(2), Excluded(3))
        );
    }

    #[test]
    fn interval_get_overlap_4() {
        let interval1 = Interval::new(Excluded(1), Excluded(3));
        let interval2 = Interval::new(Included(1), Included(4));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Excluded(1), Excluded(3))
        );
    }

    #[test]
    fn interval_get_overlap_5() {
        let interval1 = Interval::new(Unbounded, Excluded(3));
        let interval2 = Interval::new(Included(1), Included(2));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Included(1), Included(2))
        );
    }

    #[test]
    fn interval_get_overlap_6() {
        let interval1 = Interval::new(Unbounded, Excluded(3));
        let interval2 = Interval::new(Unbounded, Included(2));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Unbounded, Included(2))
        );
    }

    #[test]
    fn interval_get_overlap_7() {
        let interval1 = Interval::new(Excluded(2), Excluded(3));
        let interval2 = Interval::new(Unbounded, Included(3));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Excluded(2), Excluded(3))
        );
    }

    #[test]
    fn interval_get_overlap_8() {
        let interval1 = Interval::new(Excluded(2), Unbounded);
        let interval2 = Interval::new(Unbounded, Unbounded);

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Excluded(2), Unbounded)
        );
    }

    #[test]
    fn interval_get_overlap_9() {
        let interval1 = Interval::new(Excluded(2), Included(3));
        let interval2 = Interval::new(Excluded(3), Included(4));

        assert!(Interval::get_overlap(&interval1, &interval2).is_none());
    }

    #[test]
    fn interval_get_overlap_10() {
        let interval1 = Interval::new(Excluded(2), Included(3));
        let interval2 = Interval::new(Included(4), Included(4));

        assert!(Interval::get_overlap(&interval1, &interval2).is_none());
    }

    #[test]
    fn interval_get_overlap_11() {
        let interval1 = Interval::new(Included(3), Included(4));
        let interval2 = Interval::new(Included(2), Included(3));

        assert!(
            Interval::get_overlap(&interval1, &interval2).unwrap()
                == Interval::new(Included(3), Included(3))
        );
    }

    #[test]
    fn interval_contains_1() {
        let interval1 = Interval::new(Included(1), Included(4));
        let interval2 = Interval::new(Included(2), Included(3));

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_2() {
        let interval1 = Interval::new(Included(1), Included(4));
        let interval2 = Interval::new(Excluded(1), Included(3));

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_3() {
        let interval1 = Interval::new(Included(1), Included(4));
        let interval2 = Interval::new(Included(1), Included(3));

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_4() {
        let interval1 = Interval::new(Included(1), Included(4));
        let interval2 = Interval::new(Included(2), Excluded(4));

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_contains_5() {
        let interval1 = Interval::new(Included(1), Included(4));
        let interval2 = Interval::new(Included(2), Included(4));

        assert!(Interval::contains(&interval1, &interval2));
    }

    #[test]
    fn interval_span_1() {
        let interval1 = Interval::new(Included(2), Included(3));
        let interval2 = Interval::new(Included(2), Excluded(3));
        let interval3 = Interval::new(Excluded(2), Included(3));
        let interval4 = Interval::new(Excluded(2), Excluded(3));

        let interval5 = Interval::new(Unbounded, Excluded(3));
        let interval6 = Interval::new(Excluded(2), Unbounded);
        let interval7 = Interval::new(Unbounded, Excluded(3));
        let interval8 = Interval::new(Unbounded, Unbounded);

        assert_eq!(interval1.span(), Some(2));
        assert_eq!(interval2.span(), Some(1));
        assert_eq!(interval3.span(), Some(1));
        assert_eq!(interval4.span(), Some(0));
        assert_eq!(interval5.span(), None);
        assert_eq!(interval6.span(), None);
        assert_eq!(interval7.span(), None);
        assert_eq!(interval8.span(), None);
    }
}
