(add-pvar-name "A" "B" "C" (make-arity))


(set-goal "(A -> B -> C) -> (A -> B) -> A -> C")
(assume "f" "g" "x")
(use "f")
(use "x")
(use-with "g" "x")

(set-goal "A & B -> B & A")
(assume "f")
(split)
(use "f")
(use "f")

(set-goal "(A -> B -> C) -> A & B -> C")
(assume "f" "xandy")
(use "f")
(use "xandy")
(use "xandy")

(set-goal "((A -> B) -> A) -> A")
(assume "f")
(use "StabLog")
(assume "notA")
(use "notA")
(use "f")
(assume "x")
(use "EfqLog")
(use-with "notA" "x")

(set-goal "(A -> B) -> not B -> not A")
(assume "f" "notB" "x")
(use "notB")
(use-with "f" "x")

(set-goal "not (A -> B) -> not B")
(assume "f" "y")
(use "f")
(assume "_")
(use "y")

(set-goal "not (not (A -> B)) -> not (not A) -> not (not B)")
(assume "f" "notnotA" "notB")
(use "f")
(assume "g")
(use "notnotA")
(assume "x")
(use "notB")
(use "g")
(use "x")


(add-pvar-name "P" "Q" (make-arity (py "alpha")))
(add-var-name "x" (py "alpha"))

(set-goal "all x (P x -> Q x) -> all x P x -> all x Q x")
(assume "f" "g")
(assume "x")
(use "f")
(use "g")

(set-goal "all x (P x -> Q x) -> ex x P x -> ex x Q x")
(assume "f" "xP")
(ex-elim "xP")
(assume "x")
(assume "Px")
(ex-intro (pt "x"))
(use "f")
(use "Px")
