#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvec-prime.rkt")
(require "interp-Cvec.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "type-check-Lvec.rkt")
(debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(interp-tests "vec" type-check-Lvec compiler-passes interp-Lvec-prime "vectors_test" (tests-for "vectors"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
(compiler-tests "vec" type-check-Lvec compiler-passes "vectors_test" (tests-for "vectors"))
