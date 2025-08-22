(**
 * FibonacciDefinition - Infinite Fibonacci Sequence Definition with F₁=1, F₂=2 Convention
 * 
 * This module defines the Fibonacci sequence using our specific convention:
 * F₀=0, F₁=1, F₂=2, F₃=3, F₄=5, F₅=8, F₆=13, ...
 * 
 * SINGLE THEOREM POLICY: This file contains only the Fibonacci sequence definition.
 * ZERO ADMITTED POLICY: All theorems proven with complete proofs ending in Qed.
 * INFINITE RANGE: Works for all natural numbers through Equations plugin.
 * 
 * Mathematical Correspondence:
 * - docs/math/00-basic-notation.md § 2.1 Fibonacci序列系统
 * - docs/math/04-dynamic-programming.md § 2.1 标准Fibonacci递推
 * 
 * Dependencies: Equations plugin for Coq 9.0
 *)

(** Use Equations for better recursive definitions *)
From Equations Require Import Equations.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Module FibonacciDefinition.

(** * Fibonacci Sequence Definition using Equations *)

(**
 * Fibonacci sequence with our convention: F₀=0, F₁=1, F₂=2, F₃=3, F₄=5, F₅=8, ...
 * Using Equations for well-founded recursion on all natural numbers.
 *)
Equations fibonacci (n : nat) : nat by wf n lt :=
  fibonacci 0 := 0;
  fibonacci 1 := 1;
  fibonacci 2 := 2;
  fibonacci (S (S (S n'))) := fibonacci (S (S n')) + fibonacci (S n').

(** * Basic Properties *)

(** Verify initial values *)
Theorem fibonacci_initial_values :
  fibonacci 0 = 0 /\
  fibonacci 1 = 1 /\
  fibonacci 2 = 2 /\
  fibonacci 3 = 3 /\
  fibonacci 4 = 5 /\
  fibonacci 5 = 8 /\
  fibonacci 6 = 13 /\
  fibonacci 7 = 21 /\
  fibonacci 8 = 34 /\
  fibonacci 9 = 55 /\
  fibonacci 10 = 89.
Proof.
  repeat split; simp fibonacci; reflexivity.
Qed.

(** Recurrence equation for n ≥ 1 *)
Theorem fibonacci_equation : forall n : nat,
  n >= 1 -> fibonacci (S (S n)) = fibonacci (S n) + fibonacci n.
Proof.
  intros n Hn.
  destruct n as [|n']; [lia |].
  (* n = S n' >= 1 *)
  simp fibonacci. reflexivity.
Qed.

(** Alternative recurrence for n ≥ 3 *)
Theorem fibonacci_recurrence : forall n : nat,
  n >= 1 -> fibonacci (n + 2) = fibonacci (n + 1) + fibonacci n.
Proof.
  intros n Hn.
  destruct n as [|n']; [lia |].
  replace (S n' + 2) with (S (S (S n'))) by lia.
  replace (S n' + 1) with (S (S n')) by lia.
  simp fibonacci.
  reflexivity.
Qed.

(** * Positivity *)

(** Fibonacci is positive for n ≥ 1 *)
Theorem fibonacci_positive : forall n : nat,
  n >= 1 -> fibonacci n > 0.
Proof.
  intros n Hn.
  (* Use strong induction *)
  induction n as [n IHn] using (well_founded_induction lt_wf).
  destruct n as [|n']; [lia |].
  destruct n' as [|n''].
  - (* n = 1 *)
    simp fibonacci. lia.
  - destruct n'' as [|n'''].
    + (* n = 2 *)
      simp fibonacci. lia.
    + (* n ≥ 3 *)
      simp fibonacci.
      assert (H1: fibonacci (S (S n''')) > 0).
      { apply IHn; lia. }
      assert (H2: fibonacci (S n''') > 0).
      { apply IHn; lia. }
      lia.
Qed.

(** * Non-negativity *)

(** Fibonacci is non-negative for all n *)
Theorem fibonacci_nonnegative : forall n : nat,
  fibonacci n >= 0.
Proof.
  intros n.
  destruct n as [|n'].
  - simp fibonacci. lia.
  - apply Nat.lt_le_incl.
    apply fibonacci_positive.
    lia.
Qed.

(** * Export Interface *)

Module FibonacciDefinitionInterface.
  Definition fibonacci := fibonacci.
  Definition fibonacci_initial_values := fibonacci_initial_values.
  Definition fibonacci_equation := fibonacci_equation.
  Definition fibonacci_recurrence := fibonacci_recurrence.
  Definition fibonacci_positive := fibonacci_positive.
  Definition fibonacci_nonnegative := fibonacci_nonnegative.
End FibonacciDefinitionInterface.

End FibonacciDefinition.

(**
 * Module Summary:
 * 
 * This module provides the foundational definition of the Fibonacci sequence
 * with our specific F₁=1, F₂=2 convention, working for ALL natural numbers.
 * 
 * Key Achievements:
 * ✓ Infinite range: Works for all natural numbers
 * ✓ Uses Equations: Clean, well-founded recursive definition
 * ✓ Complete proofs: All theorems end with Qed (no Admitted)
 * ✓ Verified consistency: Initial values match our convention
 * ✓ Clean interface: Single fibonacci function for all uses
 * 
 * The definition serves as the foundation for all Fibonacci-related proofs
 * in the Zeckendorf-Hilbert theory.
 *)