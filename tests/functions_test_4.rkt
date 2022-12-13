(define (id [x : Integer]) : Integer x)
(let ([old-id id])
  (let ([id 42])
    (old-id id)))
