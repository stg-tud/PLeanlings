/-
# 03.01 — Enumerations

With `inductive` you define your *own* types by listing all the ways to
build a value of it. The simplest case is an enumeration:

    inductive Weekday where
      | monday | tuesday | wednesday | thursday | friday | saturday | sunday

Each `| name` is a **constructor**. The values of `Weekday` are exactly
`Weekday.monday`, …, `Weekday.sunday`, and they are all different.
(`deriving Repr` lets `#eval` print values; chapter 04 explains it.)

Functions on an inductive type are defined by **pattern matching**, one case
per constructor:

    def Weekday.isMonday : Weekday → Bool
      | .monday => true
      | _       => false        -- `_` matches anything else

The leading dot in `.monday` is short for `Weekday.monday`: Lean knows the
expected type. Lean checks that your patterns cover **all** cases; try
deleting a case and read the error ("missing cases").

Note the syntax: a definition by pattern matching has no `:=`; the cases
follow directly after the type.

`Bool` itself is just such an enumeration with two constructors,
`true` and `false`!

## Your task

1. `Weekday.next d` returns the following day (`sunday` is followed by
   `monday`). The first case is given; replace `| _ => sorry` by the
   remaining cases.
2. `Weekday.prev d` returns the previous day.
3. `Weekday.isWeekend d` is `true` for `saturday` and `sunday` only.

For `prev` and `isWeekend`, replace `:= sorry` by a list of cases.
-/

inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
deriving Repr

def Weekday.next : Weekday → Weekday
  | .monday    => .tuesday
  | _          => sorry

def Weekday.prev : Weekday → Weekday := sorry

def Weekday.isWeekend : Weekday → Bool := sorry
