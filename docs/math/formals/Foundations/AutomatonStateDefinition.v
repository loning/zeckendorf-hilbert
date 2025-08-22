(**
 * AutomatonStateDefinition - State Space for φ-Language Automaton
 * 
 * This module defines the state space for the finite automaton
 * that recognizes valid φ-strings (no consecutive 11).
 * 
 * SINGLE THEOREM POLICY: This file contains only state definitions.
 * ZERO ADMITTED POLICY: All theorems proven with complete proofs ending in Qed.
 * PURE BINARY POLICY: Uses inductive states, no string dependencies.
 * 
 * Mathematical Correspondence:
 * - State space for NFA/DFA recognizing φ-language
 * - Encodes "last bit seen" to enforce no-11 constraint
 * - Foundation for computational φ-string verification
 * 
 * Dependencies: PhiBitType.v
 *)

(** Standard Coq imports *)
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.

(** Import our binary foundation *)
From Foundations Require Import PhiBitType.

Module AutomatonStateDefinition.

Import PhiBitType.

(** * Automaton State Space *)

(**
 * States for the φ-language automaton
 * - q_start: initial state (no bits seen yet)
 * - q_zero: last bit was 0
 * - q_one: last bit was 1
 * - q_reject: found "11" pattern (rejection state)
 *)
Inductive AutomatonState : Type :=
  | q_start : AutomatonState
  | q_zero : AutomatonState  
  | q_one : AutomatonState
  | q_reject : AutomatonState.

(** * State Properties *)

(**
 * States are decidably equal
 *)
Theorem automaton_state_eq_dec :
  forall (s1 s2 : AutomatonState), {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct s1, s2; try (left; reflexivity); right; discriminate.
Qed.

(**
 * Acceptance states: all except q_reject
 *)
Definition is_accepting_state (s : AutomatonState) : bool :=
  match s with
  | q_reject => false
  | _ => true
  end.

(**
 * Initial state
 *)
Definition initial_state : AutomatonState := q_start.

(** * State Classification *)

(**
 * Rejection state property
 *)
Theorem q_reject_not_accepting :
  is_accepting_state q_reject = false.
Proof.
  reflexivity.
Qed.

(**
 * All other states are accepting
 *)
Theorem other_states_accepting :
  is_accepting_state q_start = true /\
  is_accepting_state q_zero = true /\
  is_accepting_state q_one = true.
Proof.
  repeat split; reflexivity.
Qed.

(**
 * Acceptance decidability
 *)
Theorem acceptance_decidable :
  forall s : AutomatonState,
    {is_accepting_state s = true} + {is_accepting_state s = false}.
Proof.
  intro s.
  destruct s; [left; reflexivity | left; reflexivity | left; reflexivity | right; reflexivity].
Qed.

(** * State Invariants *)

(**
 * The automaton has exactly 4 states
 *)
Definition all_states : list AutomatonState :=
  q_start :: q_zero :: q_one :: q_reject :: nil.

Theorem all_states_complete :
  forall s : AutomatonState, In s all_states.
Proof.
  intro s.
  destruct s; simpl; auto.
Qed.

(**
 * States are distinct (no duplicates in the complete list)
 *)
Theorem all_states_distinct :
  List.NoDup all_states.
Proof.
  unfold all_states.
  repeat constructor; simpl; intuition discriminate.
Qed.

(** * Computational Properties *)

(**
 * State space is finite
 *)
Theorem state_space_finite :
  length all_states = 4.
Proof.
  reflexivity.
Qed.

(**
 * Each state has a unique representation
 *)
Example state_distinctness :
  q_start <> q_zero /\
  q_start <> q_one /\
  q_start <> q_reject /\
  q_zero <> q_one /\
  q_zero <> q_reject /\
  q_one <> q_reject.
Proof.
  repeat split; discriminate.
Qed.

(** * Module Interface *)

(**
 * Export core state definitions
 *)
Module AutomatonStateInterface.
  Definition exported_AutomatonState := AutomatonState.
  Definition exported_q_start := q_start.
  Definition exported_q_zero := q_zero.
  Definition exported_q_one := q_one.
  Definition exported_q_reject := q_reject.
  Definition exported_is_accepting_state := is_accepting_state.
  Definition exported_initial_state := initial_state.
  Definition exported_all_states := all_states.
  Definition exported_automaton_state_eq_dec := automaton_state_eq_dec.
End AutomatonStateInterface.

End AutomatonStateDefinition.

(**
 * Module Summary:
 * 
 * This AutomatonStateDefinition module provides the atomic state space
 * for the φ-language recognition automaton.
 * 
 * Key Achievements:
 * ✓ Single focus: State definitions only
 * ✓ Complete state space: 4 states with clear semantics
 * ✓ Decidable equality: Full decision procedures
 * ✓ Acceptance criteria: Clear accepting/rejecting states
 * ✓ Finite and complete: Proven finite with no duplicates
 * 
 * This atomic module provides the foundation for:
 * - Automaton transition functions
 * - φ-language recognition algorithms
 * - Computational string validation
 * - All higher-level automaton operations
 *)

(** End of AutomatonStateDefinition module *)