#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "type-check-Lwhile.rkt")
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

(interp-tests "while" type-check-Lwhile compiler-passes interp-Lwhile "loop_test" (tests-for "loop"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;; (compiler-tests "if" type-check-Lif compiler-passes "cond_test" (tests-for "cond"))

