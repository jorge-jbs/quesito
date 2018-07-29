(define id
  (pi
    (a (Type 0))
    (pi
      (_ a)
      a))
  (lambda (a)
    (lambda (x)
      x))
  )

(define main
  Int
  ((+ ((+ 1) 2)) ((id Int) 2))
  )
