# tryCoq
![Logo](assets/logo.png)

tryCoq provides interactive equational proof with ADT type

tryCoq is an **interactive proof assistant** that takes **OCaml code** as input and allows users to **perform proofs interactively**.  
It is designed for reasoning about functional programs using techniques from **structural induction**, **equational reasoning**.

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

Interactive Proof Sequences:
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
tryCoq use OCaml package manager(OPAM) and dune

### Dependencies
First, run:
```bash
dune build
```

To install the dependency, run:
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
First, insert ocaml code location having ADT type and function definitions
tryCoq take 2 file paths
```
Enter the definition file path (1/2):
> exam.ml
```

Second, choose the proof mode
```
Choose the proof type :
1) Interactive Mode      2) Auto Mode
1
```

Second, insert conjecture that you want to prove
```
No conjecture
>>> assert forall (x:nat), add x Z = x
```

Now, you can proof interactively with tryCoq
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
<prop>  ::= "forall" <prop>
          | <expr> "=" <expr>
          | <prop>* "->" <prop>

<expr>  ::= <fun_name> <expr>*
          | <constructor> <expr>*
          | <var>
```

## Proof Language(tactic)
```
tactic           ::=
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


```markdown
| No. | tactic      | Description                 |
|------|------------------|----------------------------------|
| 7    | `assert`        | Establish lemma or theroem |
| 3    | `simpl`         | Simplify the target.           |
| 4    | `rewrite IH1`   | Rewrite goal using assumption or lemma.   |
| 2    | `induction x`   | Perform structural induction on `x`.          |
| 6    | `case x`        | Split goal into two subgoal x is true and x is false |
| 1    | `intro`        | Introduced variable or implication condtion into the context .         |
| 5    | `reflexivity`   | Solve equalities of the form `a=a`               |
| 8    | `discriminate`   | Solve propostion if assumption leads contradiction |
```



