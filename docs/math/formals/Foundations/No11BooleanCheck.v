(**
 * No11BooleanCheck - Boolean Decision Procedure for No-11 Constraint
 * 
 * This module provides a computable boolean function to check
 * whether a binary string satisfies the no-11 constraint.
 * 
 * SINGLE THEOREM POLICY: This file contains only the boolean check function.
 * ZERO ADMITTED POLICY: All theorems proven with complete proofs ending in Qed.
 * PURE BINARY POLICY: Uses PhiBit-based lists, no string dependencies.
 * 
 * Mathematical Correspondence:
 * - docs/math/00-basic-notation.md § 1.3 No-11 constraint
 * - docs/math/01-language-encoding.md § 2.1 φ-language definition
 * 
 * Dependencies: PhiBitType.v, PhiStringType.v
 *)

(** Standard Coq imports *)
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.

(** Import our binary foundations *)
From Foundations Require Import PhiBitType.
From Foundations Require Import PhiStringType.

Module No11BooleanCheck.

Import ListNotations.
Import PhiBitType.
Import PhiStringType.

(** * The No-11 Boolean Check Function *)

(**
 * Check if two consecutive bits are both ones
 * This is the pattern we want to avoid
 *)
Definition is_consecutive_ones (b1 b2 : PhiBit) : bool :=
  match b1, b2 with
  | one, one => true
  | _, _ => false
  end.

(**
 * Main boolean check function for no-11 constraint
 * Returns true if the string has NO consecutive ones
 * Returns false if the string HAS consecutive ones
 *)
Fixpoint no_11_check (s : PhiString) : bool :=
  match s with
  | [] => true  (* empty string satisfies constraint *)
  | [_] => true (* single bit always satisfies constraint *)
  | b1 :: (b2 :: rest) as tail =>
    if is_consecutive_ones b1 b2 then
      false  (* found consecutive ones, constraint violated *)
    else
      no_11_check tail  (* check the rest *)
  end.

(** * Basic Properties *)

(**
 * Empty string satisfies the constraint
 *)
Theorem no_11_check_empty :
  no_11_check [] = true.
Proof.
  reflexivity.
Qed.

(**
 * Single bit strings always satisfy the constraint
 *)
Theorem no_11_check_single :
  forall b : PhiBit, no_11_check [b] = true.
Proof.
  intro b.
  reflexivity.
Qed.

(**
 * The string "11" violates the constraint
 *)
Theorem no_11_check_eleven :
  no_11_check [one; one] = false.
Proof.
  reflexivity.
Qed.

(**
 * The string "10" satisfies the constraint
 *)
Theorem no_11_check_one_zero :
  no_11_check [one; zero] = true.
Proof.
  reflexivity.
Qed.

(**
 * The string "01" satisfies the constraint
 *)
Theorem no_11_check_zero_one :
  no_11_check [zero; one] = true.
Proof.
  reflexivity.
Qed.

(**
 * The string "00" satisfies the constraint
 *)
Theorem no_11_check_zero_zero :
  no_11_check [zero; zero] = true.
Proof.
  reflexivity.
Qed.

(** * Recursive Properties *)

(**
 * Adding a zero to any valid string preserves validity
 *)
Theorem no_11_check_append_zero :
  forall s : PhiString,
    no_11_check s = true ->
    no_11_check (s ++ [zero]) = true.
Proof.
  intros s H.
  induction s as [|b s' IHs'].
  - (* empty string *)
    reflexivity.
  - (* b :: s' *)
    destruct s' as [|b' s''].
    + (* single element *)
      simpl. destruct b; reflexivity.
    + (* at least two elements *)
      simpl in *.
      destruct (is_consecutive_ones b b') eqn:Hcons.
      * (* found consecutive ones in original string *)
        discriminate H.
      * (* no consecutive ones *)
        simpl.
        destruct (is_consecutive_ones b b') eqn:Hcons2.
        -- rewrite Hcons in Hcons2. discriminate.
        -- apply IHs'.
           exact H.
Qed.

(**
 * Adding a one to a string ending in zero preserves validity
 *)
Theorem no_11_check_zero_then_one :
  forall s : PhiString,
    no_11_check (s ++ [zero]) = true ->
    no_11_check (s ++ [zero; one]) = true.
Proof.
  intros s H.
  induction s as [|b s' IHs'].
  - (* empty string: [zero; one] *)
    reflexivity.
  - (* b :: s' *)
    destruct s' as [|b' s''].
    + (* single element: [b; zero; one] *)
      simpl. destruct b; reflexivity.
    + (* at least two elements *)
      simpl in H.
      simpl.
      destruct (is_consecutive_ones b b') eqn:Hcons.
      * (* found consecutive ones - contradiction *)
        discriminate H.
      * (* no consecutive ones, continue with recursion *)
        apply IHs'.
        exact H.
Qed.

(** * Computational Verification *)

(**
 * Test cases for common patterns
 *)
Example no_11_check_examples :
  no_11_check [zero; one; zero] = true /\
  no_11_check [one; zero; one] = true /\
  no_11_check [zero; one; zero; one] = true /\
  no_11_check [one; zero; zero; one] = true /\
  no_11_check [one; one; zero] = false /\
  no_11_check [zero; one; one] = false /\
  no_11_check [one; zero; one; one] = false.
Proof.
  repeat split; reflexivity.
Qed.

(** * Module Interface *)

(**
 * Core no-11 check interface export
 *)
Module No11BooleanInterface.
  Definition exported_no_11_check := no_11_check.
  Definition exported_is_consecutive_ones := is_consecutive_ones.
  Definition exported_no_11_check_empty := no_11_check_empty.
  Definition exported_no_11_check_single := no_11_check_single.
  Definition exported_no_11_check_eleven := no_11_check_eleven.
  Definition exported_no_11_check_append_zero := no_11_check_append_zero.
End No11BooleanInterface.

End No11BooleanCheck.

(**
 * Module Summary:
 * 
 * This No11BooleanCheck module provides the atomic boolean decision
 * procedure for the no-11 constraint in the φ-language.
 * 
 * Key Achievements:
 * ✓ Single focus: Boolean check function only
 * ✓ Minimal dependencies: Only PhiBitType and PhiStringType
 * ✓ Complete proofs: All theorems end with Qed
 * ✓ Computational verification: Function is fully computable
 * ✓ Pure binary implementation: Uses PhiBit lists, no strings
 * 
 * This atomic module provides the foundation for:
 * - φ-language membership testing
 * - Automaton acceptance verification
 * - String validity checking
 * - All higher-level constraint operations
 *)

(** End of No11BooleanCheck module *)