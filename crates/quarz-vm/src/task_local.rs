//! `Task::Local`'s bindings (#1213, docs/04): what `with` binds for its
//! block, on the current task, read by `value`.
//!
//! The bindings are an immutable list, innermost first: `with` puts a
//! node in front for its block and puts back the head it found when the
//! block ends, however it ends (`Task::Local#with`). No node is ever
//! written, so a child task given the head at its spawn keeps seeing
//! what was bound then, whatever its parent binds later.
//!
//! The running task's head is in its worker's `Interp`
//! (`Interp::bindings`): `value` and `with` touch only that cell. While
//! the task is not running, it is in the task's handle
//! (`TaskHandle::bindings`), moved there and back in
//! `Interp::resume_task`.

use crate::rc::Rc;
use crate::value::Value;

/// One binding: the key's id (`Task::Local`'s `@id`), its value, and the
/// bindings around it.
pub struct Bind {
    pub key: i64,
    pub value: Value,
    pub next: Bindings,
}

/// A task's bindings: `None` when nothing is bound (every key reads its
/// default).
pub type Bindings = Option<Rc<Bind>>;

/// `head` with `key` bound to `value` in front: the task's own node (a
/// count of its own), marked shared when a spawned task inherits it
/// (`inherit`).
pub fn bind(head: &Bindings, key: i64, value: Value) -> Bindings {
    Some(Rc::new(Bind {
        key,
        value,
        next: head.clone(),
    }))
}

/// The innermost binding of `key` in `head`, if any.
pub fn lookup(head: &Bindings, key: i64) -> Option<&Value> {
    let mut at = head.as_deref();
    while let Some(b) = at {
        if b.key == key {
            return Some(&b.value);
        }
        at = b.next.as_deref();
    }
    None
}

/// The bindings a spawned task starts with: `head`, its nodes and their
/// values marked shared (the child may run on another worker), as a
/// spawned block's captures are (`Value::share`). The walk stops at a
/// node shared already: everything below it was marked with it.
pub fn inherit(head: &Bindings) -> Bindings {
    let mut at = head.as_ref();
    while let Some(node) = at {
        if !Rc::mark_shared(node) {
            break;
        }
        node.value.share();
        at = node.next.as_ref();
    }
    head.clone()
}
