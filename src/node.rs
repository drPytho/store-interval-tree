use core::cmp::max;
use std::boxed::Box;

use crate::interval::Interval;

#[derive(Clone, Debug, Hash)]
pub(crate) struct Node<V> {
    pub interval: Option<Interval>,
    pub value: Option<Vec<V>>,
    pub max: Option<usize>,
    pub height: usize,
    pub size: usize,
    pub left_child: Option<Box<Node<V>>>,
    pub right_child: Option<Box<Node<V>>>,
}

impl<V> Node<V> {
    pub fn init(
        interval: Interval,
        value: Vec<V>,
        max: usize,
        height: usize,
        size: usize,
    ) -> Node<V> {
        Node {
            interval: Some(interval),
            value: Some(value),
            max: Some(max),
            height,
            size,
            left_child: None,
            right_child: None,
        }
    }

    pub fn value(&self) -> &Vec<V> {
        self.value.as_ref().unwrap()
    }

    // fn value_mut(&mut self) -> &mut V {
    //    self.value.as_mut().unwrap()
    //}

    pub fn get_value(&mut self) -> Vec<V> {
        self.value.take().unwrap()
    }

    pub fn append(&mut self, value: V) {
        if self.value.is_some() {
            self.value.as_mut().unwrap().push(value);
        } else {
            self.value = Some(vec![value])
        }
    }

    pub fn interval(&self) -> &Interval {
        self.interval.as_ref().expect("NO IDEA")
    }

    pub fn get_interval(&mut self) -> Interval {
        self.interval.take().expect("NO IDEA")
    }

    pub fn get_max(&self) -> usize {
        self.max.unwrap()
    }

    // _max_height is at least -1, so +1 is a least 0 - and it can never be higher than usize
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    pub fn update_height(&mut self) {
        self.height = (1 + Node::_max_height(&self.left_child, &self.right_child)) as usize;
    }

    pub fn update_size(&mut self) {
        self.size = 1 + Node::size(&self.left_child) + Node::size(&self.right_child);
    }

    pub fn update_max(&mut self) {
        let max = match (&self.left_child, &self.right_child) {
            (Some(left_child), Some(right_child)) => Node::<V>::find_max(
                self.interval().get_high(),
                Node::<V>::find_max(left_child.get_max(), right_child.get_max()),
            ),
            (Some(left_child), None) => {
                Node::<V>::find_max(self.interval().get_high(), left_child.get_max())
            }
            (None, Some(right_child)) => {
                Node::<V>::find_max(self.interval().get_high(), right_child.get_max())
            }
            (None, None) => self.interval().get_high(),
        };

        self.max = Some(max);
    }

    pub fn find_max(bound1: usize, bound2: usize) -> usize {
        bound1.max(bound2)
    }

    pub fn is_ge(bound1: &usize, bound2: &usize) -> bool {
        bound1 >= bound2
    }

    pub fn _max_height(node1: &Option<Box<Node<V>>>, node2: &Option<Box<Node<V>>>) -> i64 {
        max(Node::height(node1), Node::height(node2))
    }

    pub fn height(node: &Option<Box<Node<V>>>) -> i64 {
        match node {
            Some(node) => node.height as i64,
            None => -1,
        }
    }

    pub fn size(node: &Option<Box<Node<V>>>) -> usize {
        match node {
            Some(node) => node.size,
            None => 0,
        }
    }

    pub fn balance_factor(node: &Node<V>) -> i64 {
        Node::height(&node.left_child) - Node::height(&node.right_child)
    }
}
