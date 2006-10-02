#!/usr/bin/python
# Generate the base transforms from the data type definition in Tree.

import os, sys, re

def die(*s):
	print >>sys.stderr, "Fatal: " + "".join(map(str, s))
	sys.exit(1)

def update_def(func, f, newf):
	newf.write("\n" + func + " :: Transform st\n")
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
		name = "N." + fields[0]
		args = fields[1:]

		lhs = []
		lines = []
		rhs = []
		i = 1
		for arg in args:
			n = "a" + str(i)
			i += 1

			lhs.append(n)
			var = "v" + n
			if arg == "Node":
				lines.append(var + " <- top " + n)
				rhs.append(var)
			elif arg == "[Node]":
				lines.append(var + " <- mapM top " + n)
				rhs.append(var)
			else:
				rhs.append(n)

		space = ""
		if lhs != []:
			space = " "
		newf.write("      " + name + space + " ".join(lhs) + " -> do\n")
		for l in lines:
			newf.write("        " + l + "\n")
		newf.write("        return $ " + name + space + " ".join(rhs) + "\n")
	newf.write("      _ -> next node\n")

def main():
	f = open("Tree.hs")
	newf = open("BaseTransforms.hs", "w")

	newf.write("""-- Base transforms
-- Automatically generated from Tree.hs -- do not edit!

module BaseTransforms where

import qualified Tree as N
import Pass
import Control.Monad
""")

	while 1:
		s = f.readline()
		if s == "":
			break
		if s.startswith("-- {{{ BEGIN"):
			ss = s.strip().split()
			update_def(ss[3], f, newf)
	f.close()
	newf.close()

main()
