//! # Q
//! This library contains the implementation of the educational Q superposition prover.
//! It contains a couple of basic components that are eventually going to accumulate in a
//! superposition based proof procedure. Additionally [tptp_parser] is able to read TPTP FOF
//! problems into our internal problem formats.


pub mod clause;
pub mod clause_queue;
pub mod discr_tree;
pub mod kbo;
pub mod multi_set;
pub mod position;
pub mod pretty_print;
pub mod subst;
pub mod term_bank;
pub mod term_manager;
pub mod tptp_parser;
pub mod unify;
