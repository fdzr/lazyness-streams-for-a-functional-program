#lang play

(require "main.rkt")
(print-only-errors #t)
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+ 
#|(module+ test
  (test (run '{+ 1 1}) 2)
  
  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
  (test (run '{< 1 2}) #t)
  
  (test (run '{local {{define x 1}}
                x}) 1)
  
  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)
  
  ;; datatypes  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
        #f)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
        #f)      
  
  ;; match
  (test (run '{match 1 {case 1 => 2}}) 2)
  
  (test (run '{match 2
                {case 1 => 2}
                {case 2 => 3}})             
        3)
  
  (test (run '{match #t {case #t => 2}}) 2)
  
  (test (run '{match #f
                {case #t => 2}
                {case #f => 3}})             
        3)

  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}})
        #t)
  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t))|#

;tests for extended MiniScheme+ 

#|(module+ sanity-tests
    (test (run '{local {{datatype Nat 
                  {Zero} 
                  {Succ n}}
                {define pred {fun {n} 
                               {match n
                                 {case {Zero} => {Zero}}
                                 {case {Succ m} => m}}}}}
          {pred {Succ {Succ {Zero}}}}}) "{Succ {Zero}}")
  
(test (run
 `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1 1}")

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 10
                         {stream-zipWith
                          {fun {n m}
                               {+ n m}}
                          ones
                          ones}}}})  "{list 2 2 2 2 2 2 2 2 2 2}")
(test 
(run `{local ,stream-lib
               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                 {stream-take 10 {merge-sort fibs fibs}}}})   "{list 1 1 1 1 2 2 3 3 5 5}"))

|#

(test (run '{List? {Empty}}) #t)
  
(test (run '{Empty? {Empty}}) #t)
  
(test (run '{Cons? {Cons 1 2}}) #t)
  
(test (run '{Empty? {Cons 1 2}}) #f)
  
(test (run '{Cons? {Empty}}) #f)      
  
;; match
(test (run '{match 1 {case 1 => 2}}) 2)
  
(test (run '{match 2
              {case 1 => 2}
              {case 2 => 3}})             
      3)
  
(test (run '{match #t {case #t => 2}}) 2)
  
(test (run '{match #f
              {case #t => 2}
              {case #f => 3}})             
      3)





(test (pretty-printing (run '{local {{datatype Nat
                                         {Zero}
                                         {Succ n}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {Zero} => {Zero}}
                                                   {case {Succ m} => m}}}}}
                         {pred {Succ {Succ {Zero}}}}})) "{Succ {Zero}}")

(test (pretty-printing (run '{local {{datatype Nat
                                         {Zero}
                                         {Succ n m}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {Zero} => {Zero}}
                                                   {case {Succ n m} => m}}}}}
                         {pred {Succ {Zero}{Succ {Zero}{Zero}}}}})) "{Succ {Zero}{Zero}}")

(test (pretty-printing (run '{local {{datatype Nat
                                         {One}
                                         {Two n m}
                                         {Three n m o}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {One} => {One}}
                                                   {case {Two n m} => m}
                                                   {case {Three n m o} => o}}}}}
                         {pred {Two {One}{Three {Two {One}{One}}{One}{One}}}}})) "{Three {Two {One}{One}}{One}{One}}")

(test (pretty-printing (run '{local {{datatype Nat
                                         {Zero}
                                         {One}
                                         {Succ n m}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {Zero} => {Zero}}
                                                   {case {One} => {One}}
                                                   {case {Succ n m} => n}}}}}
                         {pred {Succ {One}{Succ {Zero}{One}}}}})) "{One}")

(test (pretty-printing (run '{local {{datatype Nat
                                         {Zero}
                                         {One}
                                         {Succ n m}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {Zero} => {Zero}}
                                                   {case {One} => {One}}
                                                   {case {Succ n m} => m}}}}}
                         {pred {Succ {One}{Succ {Succ {Zero}{Succ {One}{One}}}{One}}}}})) "{Succ {Succ {Zero}{Succ {One}{One}}}{One}}")


(test (pretty-printing (run '{local {{datatype Nat
                                         {Zero}
                                         {One}
                                         {Succ n m}}
                               {define pred {fun {n}
                                                 {match n
                                                   {case {Zero} => {Zero}}
                                                   {case {One} => {One}}
                                                   {case {Succ n m} => n}}}}}
                         {pred {Succ {One}{Succ {Succ {Zero}{Succ {One}{One}}}{One}}}}})) "{One}")

(test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t) 

(test (run '{List? {Cons 1 2}}) #t)
(test/exn (run '{List? {A 1 2}}) "no binding for identifier: A")
(test (run '{length {Empty}}) 0)
(test (run '{length {Cons 1 {Cons 2 {Cons 3 {Empty}}}}}) 3)
(test (run '{length {Cons 21 {Cons 23 {Cons 89 {Empty}}}}}) 3)
(test (run '{length {Cons 7 {Cons 11 {Cons 23 {Cons 71 {Cons 113 {Empty}}}}}}}) 5)

(test (run '{match {list {+ 1 1} 4 6}
              {case {Cons h r} => h}
              {case _ => 0}}) 2)

(test (run '{match {list {list 1 1} 4 6}
              {case {Cons {Cons h x} r} => h}
              {case _ => 0}}) 1)

(test (run '{match {list {list 1 {list 2 3 4 5 10}} 4 6}
              {case {Cons {Cons h {Cons a b}} r} => b}
              {case _ => 0}}) "{list}")

(test (run '{match {list {list 1 {list 2 3 4 5 10}} 4 6}
              {case {Cons {Cons h {Cons {Cons a {Cons e {Cons f {Cons t {Cons y {Empty}}}}}}{Empty}}} r} => y}
              {case _ => 0}}) 10)

(test (run '{match {list {list {list {list 3}}} 4}
              {case {Cons {Cons {Cons {Cons a {Empty}}{Empty}}{Empty}} r} => a}
              {case _ => 0}}) 3)

(test (run '{match {list}
              {case {Cons h r} => h}
              {case _ => 0}}) 0)

(test (run '{match {list}
              {case {Cons h r} => h}
              {case {Empty} => 0}}) 0)

(test (run '{match {list 2 {list 4 5} 6}
              {case {list a {list b c} d} => c}}) 5)

(test (run '{match {list {list 1 {list 2 3 4 5 10}} 4 6}
              {case {list {list a b} b c} => b}
              {case _ => 0}}) "{list 2 3 4 5 10}")

(test (run '{match {list {list {list {list 3}}} 4}
              {case {list a b} => a}
              {case _ => 0}}) "{list {list {list 3} } }")

(test (run '{match {list {list {list {list 3}}} 4}
              {case {list a b} => b}
              {case _ => 0}}) 4)

(test (run '{match {list {list 1 {list 2 3}} 4}
              {case {list a b} => a}
              {case _ => 0}}) "{list 1 {list 2 3} }")

(test (run '{list 1 4 6}) "{list 1 4 6}")
(test (run '{list 1 {list 1 2} 6}) "{list 1 {list 1 2}  6}")
(test (run '{list {list 7 8} {list 1 2} 6}) "{list {list 7 8}  {list 1 2}  6}")
(test (run '{list}) "{list}")

(test (run '{{fun {x {lazy y}} x} 1 {/ 1 0}}) 1)
(test (run '{{fun {x {lazy y} z} z} 1 {/ 1 0} 3}) 3)
(test (run '{{fun {{lazy x} {lazy y} {lazy z}} {+ 1 2}} {/ 3 0} {/ 2 0} {/ 1 0}}) 3)
(test (run '{{fun {{lazy x} y {lazy z}} {+ 1 y}} {/ 3 0} 5 {/ 1 0}}) 6)

(test (run '{local {{datatype T
                              {C {lazy a}}}
                    {define x {C {/ 1 0}}}}
              {T? x}}) #t)

(test (run '{local {{datatype T
                              {C {lazy a} b}}
                    {define x {C {/ 1 0} {+ 1 2}}}}
              {match x
                {case {C a b} => b}}}) 3)

(test (run '{local {{datatype T
                              {C {lazy a} {lazy b}}}
                    {define x {C {/ 1 0} {/ 1 {- 5 {+ 2 3}}}}}}
              {match x
                {case {C a b} => 1}}}) 1)


(test (run
       `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1 1}")

(test (run `{local ,stream-lib
              {local {,stream-zipWith ,fibs}
                {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
              {local {,ones ,stream-zipWith}
                {stream-take 10
                             {stream-zipWith
                              {fun {n m}
                                   {+ n m}}
                              ones
                              ones}}}})  "{list 2 2 2 2 2 2 2 2 2 2}")

(test (run `{local ,stream-lib
              {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                {stream-take 10 {merge-sort fibs fibs}}}})   "{list 1 1 1 1 2 2 3 3 5 5}")















