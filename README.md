minikanren-with-forall
==========

Copyright (C) 2025 John Misciagno

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


Example:

A "forall" expression succeeds if and only its newly introduced variables are unbound.

An "exists" expression is equivalent to a "fresh" expression.

```
(run* (q) (forall (p) (== p p))) ; => succeeds
(run* (q) (forall (p) (membero p (list p)))) ; => succeeds
(run* (q) (forall (p) (exists (r) (== p r)))) ; => succeeds
(run* (q) (forall (p) (== p 0))) ; => fails
(run* (q) (forall (p p0) (== p p0))) ; => fails
(run* (q) (exists (p) (forall (p0) (== p p0)))) ; => fails

(run* (q) (exists (p) (forall (p0) (conde ((== p p0) (== q 99))
				   ((== p p)  (== q 100)))))) ; => (100)

(run* (q) (forall (p) (exists (p0) (conde ((== p p0) (== q 99))
			      	   	  ((== p p)  (== q 100)))))) ; => (99 100)

(run* (q) (forall (p) (implies (== p 0)
			       (disj (== p 0) (== p 1))))) ; => succeeds

(run* (q) (forall (a) (implies (== a 1) (== q a)))) ; => 1

(run* (q) (forall (a) (implies  (== 0 4)
				(== 1 0)))) ; => succeeds

(run* (q) (forall (a b c) (implies (conj (== a b) (== b c))
				   (== a c))))) ; => succeeds

```
