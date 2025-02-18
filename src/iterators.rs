use core::fmt::Debug;
use std::vec::Vec;

use crate::{interval::Interval, node::Node};

/// A `find` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `Entry`.
#[derive(PartialEq, Eq, Debug)]
pub struct Entry<'a, V> {
    value: &'a Vec<V>,
    interval: &'a Interval,
}

impl<'a, V: 'a> Entry<'a, V> {
    /// Get a reference to the data for this entry
    #[must_use]
    pub fn value(&self) -> &'a Vec<V> {
        self.value
    }

    /// Get a reference to the interval for this entry
    #[must_use]
    pub fn interval(&self) -> &'a Interval {
        self.interval
    }
}

/// An `IntervalTreeIterator` is returned by `Intervaltree::find` and iterates over the entries
/// overlapping the query
#[derive(Debug)]
pub struct IntervalTreeIterator<'v, 'i, V: Clone> {
    pub(crate) nodes: Vec<&'v Node<V>>,
    pub(crate) interval: &'i Interval,
}

impl<'v, V: Clone + 'v> Iterator for IntervalTreeIterator<'v, '_, V> {
    type Item = Entry<'v, V>;

    fn next(&mut self) -> Option<Entry<'v, V>> {
        loop {
            let node_ref = self.nodes.pop()?;

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_ref().unwrap());
            }
            if node_ref.left_child.is_some()
                && node_ref.left_child.as_ref().unwrap().get_max() >= self.interval.low()
            {
                self.nodes.push(node_ref.left_child.as_ref().unwrap());
            }

            if Interval::overlaps(node_ref.interval(), self.interval) {
                return Some(Entry {
                    value: node_ref.value(),
                    interval: node_ref.interval(),
                });
            }
        }
    }
}

/// A `find_mut` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `EntryMut`. Only the data part can be mutably accessed
/// using the `data` method
#[derive(PartialEq, Eq, Debug)]
pub struct EntryMut<'a, V> {
    value: &'a mut Vec<V>,
    interval: &'a Interval,
}

impl<'a, V: 'a> EntryMut<'a, V> {
    /// Get a mutable reference to the data for this entry
    pub fn value(&'a mut self) -> &'a mut Vec<V> {
        self.value
    }

    /// Get a reference to the interval for this entry
    #[must_use]
    pub fn interval(&self) -> &'a Interval {
        self.interval
    }
}

/// An `IntervalTreeIteratorMut` is returned by `Intervaltree::find_mut` and iterates over the entries
/// overlapping the query allowing mutable access to the data `D`, not the `Interval`.
#[derive(Debug)]
pub struct IntervalTreeIteratorMut<'v, 'i, V: Clone> {
    pub(crate) nodes: Vec<&'v mut Node<V>>,
    pub(crate) interval: &'i Interval,
}

impl<'v, V: Clone + 'v> Iterator for IntervalTreeIteratorMut<'v, '_, V> {
    type Item = EntryMut<'v, V>;

    fn next(&mut self) -> Option<EntryMut<'v, V>> {
        loop {
            let node_ref = self.nodes.pop()?;

            let overlaps = Interval::overlaps(node_ref.interval(), self.interval);

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_mut().unwrap());
            }
            if node_ref.left_child.is_some()
                && node_ref.left_child.as_ref().unwrap().get_max() >= self.interval.low()
            {
                self.nodes.push(node_ref.left_child.as_mut().unwrap());
            }

            if overlaps {
                return Some(EntryMut {
                    value: &mut node_ref.value,
                    interval: &mut node_ref.interval,
                });
            }
        }
    }
}
