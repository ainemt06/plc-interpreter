#lang racket

(require "simpleParser.rkt")

; statement list 	<statementlist> ::= <statement> <statementlist> | nothing
; (statement1 statement2 ...)
; statement 	<statement> ::= <declare> | <assign> | <return> | <if> | <while>
; variable declaration 	<declare> ::= var <name>; | var <name> = <expression>;
; (var variable optional-value)
; assignment 	<assign> ::=  <name> = <expresson>;
; (= variable expression)
; return 	<return> ::= return <expression>;
; (return expression)
; if statement 	<if> ::= if (<condition>) <statement> | if (<condition>) <statement> else <statement>
; (if condition then-statement optional-else-statement)
; while statement 	<while> ::= while (<condition>) <statement>
; (while condition body-statement)
; expression 	<expression> ::= <condition> | <int value>
; condition 	<condition> ::= true | false | <name> | <condition> && <condition> | <condition> || <condition> | !<condition> | <int value> < <int value> | <int value> <= <int value> | <int value> > <int value> | <int value> >= <int value> | <expression> == <expression> | <expression> != <expression> 
; (&& condition condition)
; int value 	<int value> ::= <number> | <name> | <int value> + <int value> | <int value> - <int value> | <int value> * <int value> | <int value> / <int value> | <int value> % <int value> | - <int value>
; (+ intvalue intvalue)