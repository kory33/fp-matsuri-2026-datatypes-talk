namespace SystemTExamples

structure Pair (α β : Type) where
  first  : α
  second : β

-- We are "defining" these functions here since we are working inside Lean, but in the pure System T,
-- we *postulate* families of constants for pair, first, and second.

-- constructor
def pair {α β : Type} : α → β → Pair α β
| a, b => { first := a, second := b }

-- eliminators
def first {α β : Type} : Pair α β → α   := fun p => p.first
def second {α β : Type} : Pair α β → β  := fun p => p.second

-- We are "overriding" the definitions of Nat/Bool from the standard library
-- by placing these definitions inside a namespace.

inductive Bool : Type
| true : Bool
| false : Bool

-- constructors
def true : Bool := Bool.true
def false : Bool := Bool.false

-- eliminator
def foldBool {α : Type} : Bool → α → α → α
| Bool.true,  x, y => x
| Bool.false, x, y => y


inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

-- constructors
def zero : Nat := Nat.zero
def succ : Nat → Nat := Nat.succ

-- eliminator
def foldNat {α : Type} : Nat → α → (α → α) → α
| Nat.zero,     init, f => init
| (Nat.succ n), init, f => f (foldNat n init f)

-- all basic functions on Bool can be defined *just using* foldBool.
def not : Bool → Bool := λ b => foldBool b false true
def and : Bool → Bool → Bool := λ b1 => λ b2 => foldBool b1 b2 false
def or  : Bool → Bool → Bool := λ b1 => λ b2 => foldBool b1 true b2

-- Tests:
namespace BoolBasicTests
theorem notTrue  : not true = false := rfl
theorem notFalse : not false = true := rfl

theorem andTrueTrue   : and true true   = true := rfl
theorem andTrueFalse  : and true false  = false := rfl
theorem andFalseTrue  : and false true  = false := rfl
theorem andFalseFalse : and false false = false := rfl

theorem orTrueTrue   : or true true   = true := rfl
theorem orTrueFalse  : or true false  = true := rfl
theorem orFalseTrue  : or false true  = true := rfl
theorem orFalseFalse : or false false = false := rfl
end BoolBasicTests

-- basic arithmetic functions on Nat can be defined *just using* foldNat.
def one : Nat := succ zero
def add := λ (n1 : Nat) => λ (n2 : Nat) => foldNat n1 n2 (λ x => succ x)
def mul := λ (n1 : Nat) => λ (n2 : Nat) => foldNat n1 zero (λ x => add n2 x)
def exp := λ (n1 : Nat) => λ (n2 : Nat) => foldNat n2 (succ zero) (λ x => mul n1 x)

def isEven : Nat → Bool := λ n => foldNat n true (λ b => not b)
def isOdd : Nat → Bool := λ n => foldNat n false (λ b => not b)

def isZero : Nat → Bool := λ n => foldNat n true (λ b => false)

-- Tests:
namespace NatBasicTests
def two : Nat := succ one
def three : Nat := succ two

theorem addTwoOne : add two one = three := rfl
theorem mulTwoThree : mul two three = add three three := rfl
theorem expTwoThree : exp two three = mul two (mul two two) := rfl

theorem isEvenZero  : isEven zero  = true := rfl
theorem isEvenOne   : isEven one   = false := rfl
theorem isEvenTwo   : isEven two   = true := rfl
end NatBasicTests

namespace NatBasicSelfInvokingDefs

-- These definitions are "self-invoking" in the sense that
-- the function bodies refer to the function being defined,
-- but since these definitions are *progressive* and strictly reduce the argument size,
-- they can be translated into a definition using foldNat.

def addRec (n2 : Nat) : Nat → Nat
| Nat.zero     => n2
| (Nat.succ n1) => succ (addRec n2 n1)

def mulRec (n2 : Nat) : Nat → Nat
| Nat.zero     => zero
| (Nat.succ n1) => addRec n2 (mulRec n2 n1)

end NatBasicSelfInvokingDefs

end SystemTExamples
