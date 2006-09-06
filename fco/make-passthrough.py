#!/usr/bin/python
# Update the boring bass passes from the data type definition in Tree.

import os, sys, re

def die(*s):
	print >>sys.stderr, "Fatal: " + "".join(map(str, s))
	sys.exit(1)

def update_def(fn, func, f):
	origf = open(fn)
	newf = open(fn + ".new", "w")

	while True:
		s = origf.readline()
		if s == "":
			die("Couldn't find start marker for ", func, " in ", fn)
		newf.write(s)
		if s.strip().startswith("-- {{{ BEGIN " + func):
			break

	newf.write(func + " :: Pass\n")
	newf.write(func + " next top node\n")
	newf.write("  = case node of\n")
	while True:
		s = f.readline()
		if s == "":
			die("Unexpected EOF during Node definition")
		elif s.strip().startswith("-- }}} END"):
			break

		s = s.strip()
		if s == "" or s.startswith("--"):
			continue
		s = s.replace("| ", "")

		fields = s.split()
		name = fields[0]
		args = fields[1:]

		lhs = []
		rhs = []
		i = 0
		for arg in args:
			n = "abcdefghijklm"[i]
			i += 1

			lhs.append(n)
			if arg == "Node":
				rhs.append("(top " + n + ")")
			elif arg == "[Node]":
				rhs.append("(map top " + n + ")")
			else:
				rhs.append(n)

		space = ""
		if lhs != []:
			space = " "
		newf.write("      " + name + space + " ".join(lhs) + " -> " + name + space + " ".join(rhs) + "\n")
	newf.write("      _ -> next node\n")

	while True:
		s = origf.readline()
		if s == "":
			die("Couldn't find end marker for ", func, " in ", fn)
		if s.strip().startswith("-- }}} END"):
			newf.write(s)
			break

	newf.write(origf.read())

	origf.close()
	newf.close()
	os.rename(fn + ".new", fn)

def main():
	f = open("Tree.hs")
	while 1:
		s = f.readline()
		if s == "":
			break
		if s.startswith("-- {{{ BEGIN"):
			ss = s.strip().split()
			update_def(ss[3], ss[4], f)
	f.close()

main()
