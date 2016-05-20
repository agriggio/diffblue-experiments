(set-option :produce-models true)
; string support via PASS-style quantified arrays
(define-sort cprover.Char () (_ BitVec 8))
(define-sort cprover.Pos () (_ BitVec 32))
(define-sort cprover.String () (Array cprover.Pos cprover.Char))
(declare-fun cprover.str.len (cprover.String) cprover.Pos)

(declare-fun s () cprover.String)
(declare-fun s1 () cprover.String)
(declare-fun s2 () cprover.String)

;; string concat
(assert (forall ((?n cprover.Pos))
                (=> (bvult ?n (cprover.str.len s1))
                    (= (select s1 ?n) (select s ?n)))))
(assert (forall ((?n cprover.Pos))
                (=> (bvult ?n (cprover.str.len s2))
                    (= (select s2 ?n)
                       (select s (bvadd (cprover.str.len s1) ?n))))))
(assert (= (cprover.str.len s)
           (bvadd (cprover.str.len s1) (cprover.str.len s2))))

(define-fun c.p () cprover.Char (_ bv32 8))
(define-fun c.i () cprover.Char (_ bv33 8))
(define-fun c.o () cprover.Char (_ bv34 8))

(assert (= (select s2 (_ bv0 32)) c.p))
(assert (= (select s2 (_ bv1 32)) c.i))
(assert (= (select s2 (_ bv2 32)) c.p))
(assert (= (select s2 (_ bv3 32)) c.p))
(assert (= (select s2 (_ bv4 32)) c.o))
(assert (= (cprover.str.len s2) (_ bv5 32)))

(declare-fun po () cprover.String)
(assert (= (cprover.str.len po) (_ bv2 32)))
(assert (= (select po (_ bv0 32)) c.p))
(assert (= (select po (_ bv1 32)) c.o))

;; string suffix negated
(declare-fun check () Bool)
(declare-fun idx () cprover.Pos)
(assert (=> (not check)
            (or (bvult (cprover.str.len s) (cprover.str.len po))
            (and (bvult idx (cprover.str.len po))
                 (not (= (select po idx)
                         (select s (bvadd (bvsub (cprover.str.len s)
                                               (cprover.str.len po)) idx))))))))

(assert (=> check (bvuge (cprover.str.len s) (cprover.str.len po))))
(assert (forall ((?n cprover.Pos))
                (=> (and check (bvult ?n (cprover.str.len po)))
                    (= (select po ?n)
                       (select s (bvadd (bvsub (cprover.str.len s)
                                               (cprover.str.len po)) ?n))))))

(assert (not check))

(assert (bvule (cprover.str.len s1) (_ bv2147483647 32)))

(check-sat)
(get-value ((cprover.str.len s) (cprover.str.len s1) (cprover.str.len s2)))

