;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname sudoku) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor mixed-fraction #f #t none #f () #t)))
;;
;; ******************************
;; Samuel Zhang (21176009)
;; CS135 Fall 2025
;; Assignment 10
;; ******************************
;;


;; A (matrixof X) is a (listof (listof X))
;; Requires: all (listof X) have the same length

;; A Cell is a (anyof Nat (listof Nat))
;; Requires:
;; * all Nat values are positive
;; * list values contain no duplicates and are in increasing order

;; A Puzzle is a (matrixof Cell)

;; A Single is a (list Nat)

;; A Solution is a (matrixof Nat)


;; all-satisfy?: (X -> Bool) (matrixof X) -> Bool
(define (all-satisfy? pred? matrix)
  (foldl (lambda (row row-res)
           (and row-res (foldr (lambda (x res)
                                 (and (pred? x) res))
                               true row)))
         true matrix))

;; any-satisfy?: (X -> Bool) (matrixof X) -> Bool
(define (any-satisfy? pred? matrix)
  (not (all-satisfy? (lambda (x) (not (pred? x))) matrix)))

;; Unused in actual sudoku algorithm, included for assignment marks
;; find-where: (X -> Bool) (matrixof X) -> (list Nat Nat)
;; Requires: At least one element in matrix satisfies the predicate
(define (find-where pred? matrix)
  (local
    [; find/row: (listof X) Nat Nat -> (anyof empty (list Nat Nat))
     (define (find/row row c r)
       (cond [(empty? row) empty]
             [(pred? (first row)) (list c r)]
             [else (find/row (rest row) (add1 c) r)]))

     ; find: (matrixof X) Nat -> (anyof empty (list Nat Nat))
     (define (find matrix r)
       (local
         [(define result (find/row (first matrix) 0 r))]
         (cond [(empty? result) (find (rest matrix) (add1 r))]
               [else result])))]

    ; function body
    (find matrix 0)))

;; Used in place of find-where
;; find-first: (X -> Bool) (matrixof X) -> (anyof empty (list X Nat Nat))
(define (find-first pred? matrix)
  (local
    [; find/row: (listof X) Nat Nat -> (anyof empty (list X Nat Nat))
     (define (find/row row c r)
       (cond [(empty? row) empty]
             [(pred? (first row)) (list (first row) c r)]
             [else (find/row (rest row) (add1 c) r)]))

     ; find: (matrixof X) Nat -> (anyof empty (list X Nat Nat))
     (define (find matrix r)
       (cond [(empty? matrix) empty]
             [else (local
                     [(define result (find/row (first matrix) 0 r))]
                     (cond [(empty? result) (find (rest matrix) (add1 r))]
                           [else result]))]))]

    ; function body
    (find matrix 0)))

;; strings->puzzle: (listof Str) -> Puzzle
;; Requires: Str values contain only digits and question marks
(define (strings->puzzle puzzle)
  (map (lambda (row)
         (map (lambda (cell)
                (cond [(char=? #\? cell) (build-list (length puzzle) add1)]
                      [else (list (- (char->integer cell) 48))]))
              (string->list row)))
       puzzle))

;; remove-singles: Puzzle -> Puzzle
(define (remove-singles puzzle)
  (local
    [; single?: Any -> Bool
     (define (single? x)
       (and (cons? x) (empty? (rest x))
            (integer? (first x)) (<= 0 (first x))))

     ; cell-remove: Cell Nat -> Cell
     (define (cell-remove cell n)
       (cond [(integer? cell) cell]
             [else (filter (lambda (x) (not (= x n))) cell)]))

     ; simplify: Puzzle Nat Nat Int -> Puzzle
     (define (simplify puzzle n c r)
       (local
         [; simplify/col: (listof Cell) Nat -> (listof Cell)
          (define (simplify/col row c)
            (cond [(zero? c) (cons (cell-remove (first row) n) (rest row))]
                  [else (cons (first row) (simplify/col (rest row) (sub1 c)))]))

          ; simplify/row: (listof Cell) Int -> (listof Cell)
          (define (simplify/row row c)
            (cond [(empty? row) row]
                  [(zero? c) (cons n (simplify/row (rest row) -1))]
                  [else (cons (cell-remove (first row) n)
                              (simplify/row (rest row) (sub1 c)))]))]

         ; function body
         (cond [(empty? puzzle) empty]
               [(zero? r) (cons (simplify/row (first puzzle) c)
                                (simplify (rest puzzle) n c -1))]
               [else (cons (simplify/col (first puzzle) c)
                           (simplify (rest puzzle) n c (sub1 r)))])))]

    ; function body
    (cond [(not (any-satisfy? single? puzzle)) puzzle]
          [else (local
                  [(define single (find-first single? puzzle))]
                  (remove-singles (simplify puzzle (first (first single))
                                            (second single) (third single))))])))

;; solve-latin: (Puzzle -> Bool) Puzzle -> (anyof Solution empty)
(define (solve-latin constraints? puzzle)
  (local
    [; impossible?: Puzzle -> Bool
     (define (impossible? puzzle)
       (any-satisfy? empty? puzzle))

     ; solution?: Puzzle -> Bool
     (define (solution? puzzle)
       (and (all-satisfy? integer? puzzle) (constraints? puzzle)))

     ; set: Puzzle Nat Nat Nat -> Puzzle
     (define (set puzzle n c r)
       (local
         [; set/col: (listof Cell) Nat -> (listof Cell)
          (define (set/col row c)
            (cond [(zero? c) (cons n (rest row))]
                  [else (cons (first row) (set/col (rest row) (sub1 c)))]))]

         ; function body
         (cond [(zero? r) (cons (set/col (first puzzle) c) (rest puzzle))]
               [else (cons (first puzzle) (set (rest puzzle) n c (sub1 r)))])))

     ; solve: Puzzle -> (anyof Solution empty)
     (define (solve puzzle)
       (cond [(solution? puzzle) puzzle]
             [(impossible? puzzle) empty]
             [else (local
                     [(define single (find-first list? puzzle))]
                     (cond [(empty? single) empty]
                           [else (solve/list puzzle (first single)
                                             (second single) (third single))]))]))

     ; solve/list: Puzzle (listof Nat) Nat Nat -> (anyof Solution empty)
     (define (solve/list puzzle guesses c r)
       (cond [(empty? guesses) empty]
             [else (local
                     [(define result
                        (solve (remove-singles (set puzzle (list (first guesses)) c r))))]
                     (cond [(empty? result) (solve/list puzzle (rest guesses) c r)]
                           [else result]))]))]

    ; function body
    (solve (remove-singles puzzle))))

;; sudoku?: Solution -> Bool
;; Requires: input matrix must be of size 9
(define (sudoku? solution)
  (local
    [; subsquare?: (list Nat Nat Nat Nat Nat Nat Nat Nat Nat) -> Bool
     (define (subsquare? square)
       (empty? (foldl (lambda (n lst) (filter (lambda (i) (not (= n i))) lst))
                      '(1 2 3 4 5 6 7 8 9) square)))

     ; sudoku?/row: (list (list Nat Nat Nat Nat Nat Nat Nat Nat Nat)
     ;                    (list Nat Nat Nat Nat Nat Nat Nat Nat Nat)
     ;                    (list Nat Nat Nat Nat Nat Nat Nat Nat Nat)) -> Bool
     (define (sudoku?/row row)
       (cond [(and (empty? (first row)) (empty? (second row)) (empty? (third row))) true]
             [else (and (subsquare?
                         (list (first (first row))  (second (first row))  (third (first row))
                               (first (second row)) (second (second row)) (third (second row))
                               (first (third row))  (second (third row))  (third (third row))))
                        (sudoku?/row (list (rest (rest (rest (first row))))
                                           (rest (rest (rest (second row))))
                                           (rest (rest (rest (third row)))))))]))]

    ; function body
    (cond [(empty? solution) true]
          [else (and (sudoku?/row (list (first solution) (second solution) (third solution)))
                     (sudoku? (rest (rest (rest solution)))))])))




;; Test cases
(check-expect (all-satisfy? integer? '((2 3 4) (5 6 7))) true)
(check-expect (all-satisfy? integer? '((2 3 4) (5 six 7))) false)

(check-expect (any-satisfy? symbol? '((2 3 4) (5 6 7))) false)
(check-expect (any-satisfy? symbol? '((2 3 4) (5 six 7))) true)

(define F '((1 2 3 4) (4 5 (3 6) (1 2)) ((7) 8 9 ())))
(check-expect (find-where list? F) '(2 1))
(check-expect (find-where empty? F) '(3 2))
(check-expect (find-where integer? F) '(0 0))

(check-expect (find-first number? empty) empty)
(check-expect (find-first list? F) '((3 6) 2 1))
(check-expect (find-first empty? F) '(() 3 2))
(check-expect (find-first integer? F) '(1 0 0))
(check-expect (find-first symbol? F) empty)



(define 23puzzle (strings->puzzle '("???"
                                    "?3?"
                                    "??2")))
(define 324puzzle (strings->puzzle '("??3?"
                                     "??2?"
                                     "?4??"
                                     "????")))
(define (yes x) true)
(define (no x) false)
(define (diagonal-has-2? p)
  (and (not (empty? p))
       (or (= 2 (first (first p)))
           (diagonal-has-2? (map rest (rest p))))))


(check-expect (strings->puzzle empty) empty)
(check-expect 23puzzle '(( (1 2 3) (1 2 3) (1 2 3) )
                         ( (1 2 3) (3    ) (1 2 3) )
                         ( (1 2 3) (1 2 3) (2    ) )))
(check-expect 324puzzle '(( (1 2 3 4) (1 2 3 4) (3      ) (1 2 3 4) )
                          ( (1 2 3 4) (1 2 3 4) (2      ) (1 2 3 4) )
                          ( (1 2 3 4) (4      ) (1 2 3 4) (1 2 3 4) )
                          ( (1 2 3 4) (1 2 3 4) (1 2 3 4) (1 2 3 4) )))
(check-expect (diagonal-has-2? '((3 2 1)
                                 (2 1 3)
                                 (1 3 1))) false)


(check-expect (remove-singles 23puzzle) '((1 2 3)
                                          (2 3 1)
                                          (3 1 2)))
(check-expect (remove-singles 324puzzle)
              '(( (1 2   4) (1 2    ) 3         (1 2   4) )
                ( (1   3 4) (1   3  ) 2         (1   3 4) )
                ( (  2 3  ) 4         1         (  2 3  ) )
                ( (1 2 3  ) (1 2 3  ) 4         (1 2 3  ) )))


(check-expect (solve-latin yes 23puzzle) '((1 2 3)
                                           (2 3 1)
                                           (3 1 2)))
(check-expect (solve-latin yes 324puzzle) '((1 2 3 4)
                                            (4 1 2 3)
                                            (3 4 1 2)
                                            (2 3 4 1)))
(check-expect (solve-latin no 324puzzle) empty)
(check-expect (solve-latin diagonal-has-2? 324puzzle)
              '((1 2 3 4)
                (4 3 2 1)
                (2 4 1 3)
                (3 1 4 2)))
(check-expect (solve-latin yes (strings->puzzle '("?7????1?8"
                                                  "??5?1??8?"
                                                  "?6?7?5???"
                                                  "2??93????"
                                                  "3?1???8?6"
                                                  "????28??1"
                                                  "???2?7?1?"
                                                  "?1??4?2??"
                                                  "8?2????6?")))
              '((4 7 3 5 6 2 1 9 8)
                (6 2 5 3 1 4 7 8 9)
                (1 6 4 7 8 5 9 3 2)
                (2 4 8 9 3 1 6 7 5)
                (3 5 1 4 7 9 8 2 6)
                (7 3 9 6 2 8 5 4 1)
                (5 8 6 2 9 7 3 1 4)
                (9 1 7 8 4 6 2 5 3)
                (8 9 2 1 5 3 4 6 7)))


(check-expect (sudoku? '((1 2 3 4 5 6 7 8 9)
                         (4 6 5 7 8 9 1 2 3)
                         (7 8 9 1 2 3 4 5 6)
                         (4 5 6 7 8 9 1 2 3)
                         (1 2 3 4 5 6 7 8 9)
                         (7 8 9 1 2 3 4 5 6)
                         (7 8 9 1 2 3 6 5 4)
                         (4 5 6 7 8 9 1 2 3)
                         (3 2 1 4 5 6 7 8 9))) true)
(check-expect (sudoku? '((1 2 3 4 5 6 7 8 9)
                         (4 5 6 7 8 9 1 2 3)
                         (7 8 9 1 2 3 4 5 6)
                         (4 5 6 7 8 9 1 2 3)
                         (1 2 3 4 5 6 7 8 9)
                         (7 8 9 1 2 3 4 5 6)
                         (7 8 9 1 2 3 4 5 7)
                         (4 5 6 7 8 9 1 2 3)
                         (1 2 3 4 5 6 7 8 9))) false)
(check-expect (sudoku? '((0 0 0 0 0 0 0 0 0)
                         (100 100 100 100 100 100 100 100 100)
                         (0 0 0 0 0 0 0 0 0)
                         (100 100 100 100 100 100 100 100 100)
                         (0 0 0 0 0 0 0 0 0)
                         (100 100 100 100 100 100 100 100 100)
                         (0 0 0 0 0 0 0 0 0)
                         (100 100 100 100 100 100 100 100 100)
                         (0 0 0 0 0 0 0 0 0))) false)


(check-expect (solve-latin sudoku? (strings->puzzle '("48?9?2???"
                                                      "?93??5?86"
                                                      "6??3???1?"
                                                      "???5?1?9?"
                                                      "????9????"
                                                      "?3?2?6???"
                                                      "?7???3??5"
                                                      "24?1??36?"
                                                      "???6?4?27")))
              '((4 8 1 9 6 2 7 5 3)
                (7 9 3 4 1 5 2 8 6)
                (6 5 2 3 8 7 4 1 9)
                (8 2 7 5 3 1 6 9 4)
                (1 6 4 7 9 8 5 3 2)
                (5 3 9 2 4 6 8 7 1)
                (9 7 6 8 2 3 1 4 5)
                (2 4 5 1 7 9 3 6 8)
                (3 1 8 6 5 4 9 2 7)))