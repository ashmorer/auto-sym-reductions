(set-option :produce-proofs true)
(set-logic HORN)
(declare-fun bad(Int Int Int) Bool)
(declare-fun init(Int Int Int) Bool)
(declare-fun inv(Int Int Int) Bool)

(assert (forall ((s Int) (l Int) (r Int)) (=> (and
		    	    	    	      (= s 2)
					      (not(= l 2))
					      (not(= r 1)) )
					  (bad s l r))))
            
(assert (forall ((s Int) (l Int) (r Int)) 
    (=> (and (= s 0) (= l 0) (= r 0))
        (init s l r))))

(assert (forall ((s Int) (l Int) (r Int))
  (=> (init s l r)
      (inv s l r))))
      
(assert (forall ((s Int) (l Int) (r Int))
  (=> (inv s l r) (not (bad s l r)))
))

(assert (forall ((s Int) (l Int) (r Int))
  (=> (inv 0 l r)
      (inv 1 l r)
  )))

(assert (forall ((s Int) (l Int) (r Int))
  (=> (inv 1 0 r)
      (inv 1 2 r)
  )))
  
(assert (forall ((s Int) (l Int) (r Int))
  (=> (inv 1 l 0)
      (inv 1 l 1)
  )))

(assert (forall ((s Int) (l Int) (r Int))
	(=>
	(inv 1 2 1)
	(inv 2 2 1)
	)))

(assert (forall ((s Int) (l Int) (r Int))
	(=>
	(inv 2 l r)
	(inv 0 0 0)
	)))


(check-sat)
(get-model)