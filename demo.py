#-*- coding: utf-8 -*-
# Demo parser from the README.

from pyparse import Parser

p = Parser({
	"factor": ["INT", "( expr )"],
	"mul": "term * factor",
	"div": "term / factor",
	"term": ["mul", "div", "factor"],
	"add": "expr + term",
	"sub": "expr - term",
	"expr": ["add", "sub", "term"],
	"calc$": "expr"
})

p.token("INT", r"\d+")
p.emit(["INT", "mul", "div", "add", "sub", "calc"])

p.dump(p.parse("1 + 2 * (3 + 4) + 5"))
