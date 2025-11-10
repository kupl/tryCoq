# tryCoq
![Logo](assets/logo.png)

**tryCoq** provides an **interactive equational proof system** for programs defined with **algebraic data types (ADTs)**.

It is an **interactive proof assistant** that takes **OCaml code** as input and allows users to **perform proofs interactively**.  
tryCoq is designed for reasoning about functional programs using techniques such as **structural induction** and **equational reasoning**.

---

## Example

Input (OCaml function):
```ocaml
type nat = Z | S of nat

let rec add x y =
  match x with
  | Z -> y
  | S n -> S (add n y)
```

Goal (to prove interactively):
```
forall (x:nat), add x Z = x
```

Interactive Proof Sequence:
```
>>> induction x
>>> simpl
>>> reflexivity
>>> simpl
>>> rewrite IH1 in goal at *
>>> reflexivity
```

---

## Getting Started
### Requirements
tryCoq uses the OCaml package manager (OPAM) and dune as its build system.

### Dependencies
First, build the project:
```bash
dune build
```

To install the dependency:
```bash
opam install . --deps-only
```

### Run
```bash
$ dune exec tryCoq
Enter the definition file path (1/2):
>
```

---

## Interactive Proving
1️⃣ **Provide OCaml code containing ADT and function definitions**
tryCoq requires two file paths as input:
```
Enter the definition file path (1/2):
> exam.ml
```

2️⃣ **Choose the proof mode**
```
Choose the proof type :
1) Interactive Mode      2) Auto Mode
1
```

3️⃣ **Enter the conjecture to prove**
```
No conjecture
>>> assert forall (x:nat), add x Z = x
```

Now, you can perform an interactive proof with tryCoq:
```
1st goal of : forall (nat1:nat), add (nat1) (0) = nat1

---------------------------------------
forall (nat1:nat), add (nat1) (0) = nat1

0 goal(s) more...

0 conjecture(s) more...

>>> induction nat
...
```

## Proposition Language
```
<prop>           ::= "forall" <prop>
                  | <expr> "=" <expr>
                  | <prop>* "->" <prop>

<expr>           ::= <fun_name> <expr>*
                  | <constructor> <expr>*
                  | <var>
```

## Proof Language(Tactics)
```
<tactic>         ::=
                  | "assert" <prop>
                  | "simpl"
                  | "simpl in" <target_label> 
                  | "rewrite" <rewrite_label> "in" <target_label> "at" <loc>
                  | "induction" <var>
                  | "case" <expr>
                  | "intro" <var>
                  | "intro" <fact_label>
                  | "reflexivity"
                  | "discriminate"

<target_label>  ::= <fact_label> | "goal"
<rewrite_label> ::= <fact_label> | <lemma_label>
<loc>           ::= "*" | "1" | "2" | ...
<fact_label>    ::= "IH1" | "Case1" | "Cond1" | ...
<lemma_label>   ::= "lemma1" | ...
<var>           ::= "x" | "y" | ...
```
---


## Proof Language Description

| No. | Tactic | Description |
|-----|---------|-------------|
| 1 | `assert` | Introduce a new lemma or theorem to be proven. |
| 2 | `simpl` | Simplify the current goal. |
| 3 | `rewrite IH1` | Rewrite the goal using an assumption or lemma. |
| 4 | `induction x` | Perform structural induction on variable `x`. |
| 5 | `case x` | Split the goal into subgoals for different cases of `x`. |
| 6 | `intro` | Introduce a variable or implication into the context. |
| 7 | `reflexivity` | Solve goals of the form `a = a`. |
| 8 | `discriminate` | Solve a goal if an assumption leads to a contradiction. |
