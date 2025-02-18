use core::cmp::max;
use std::boxed::Box;

use crate::interval::Interval;

#[derive(Clone, Debug, Hash)]
pub(crate) struct Node<V: Clone> {
    pub interval: Interval,
    pub value: Vec<V>,
    pub max: usize,
    pub height: usize,
    pub size: usize,
    pub left_child: Option<Box<Node<V>>>,
    pub right_child: Option<Box<Node<V>>>,
}

impl<V: Clone> Node<V> {
    pub fn init(
        interval: Interval,
        value: Vec<V>,
        max: usize,
        height: usize,
        size: usize,
    ) -> Node<V> {
        Node {
            interval,
            value,
            max,
            height,
            size,
            left_child: None,
            right_child: None,
        }
    }

    pub fn value(&self) -> &Vec<V> {
        &self.value
    }

    pub fn get_value(&mut self) -> Vec<V> {
        self.value.clone()
    }

    pub fn append(&mut self, value: V) {
        self.value.push(value);
    }

    pub fn interval(&self) -> &Interval {
        &self.interval
    }

    pub fn get_interval(&mut self) -> Interval {
        self.interval
    }

    pub fn get_max(&self) -> usize {
        self.max
    }

    // _max_height is at least -1, so +1 is a least 0 - and it can never be higher than usize
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    pub fn update_height(&mut self) {
        self.height =
            (1 + Node::_max_height(self.left_child.as_deref(), self.right_child.as_deref()))
                as usize;
    }

    pub fn update_size(&mut self) {
        self.size =
            1 + Node::size(self.left_child.as_deref()) + Node::size(self.right_child.as_deref());
    }

    pub fn update_max(&mut self) {
        self.max = match (&self.left_child, &self.right_child) {
            (Some(left_child), Some(right_child)) => self
                .interval()
                .high()
                .max(left_child.max)
                .max(right_child.max),
            (Some(left_child), None) => self.interval().high().max(left_child.max),
            (None, Some(right_child)) => self.interval().high().max(right_child.max),
            (None, None) => self.interval().high(),
        };
    }

    pub fn _max_height(node1: Option<&Node<V>>, node2: Option<&Node<V>>) -> i64 {
        max(Node::height(node1), Node::height(node2))
    }

    pub fn height(node: Option<&Node<V>>) -> i64 {
        match node {
            Some(node) => node.height as i64,
            None => -1,
        }
    }

    pub fn size(node: Option<&Node<V>>) -> usize {
        match node {
            Some(node) => node.size,
            None => 0,
        }
    }

    pub fn balance_factor(node: &Node<V>) -> i64 {
        Node::height(node.left_child.as_deref()) - Node::height(node.right_child.as_deref())
    }
}
