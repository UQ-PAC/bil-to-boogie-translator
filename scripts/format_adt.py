#!/usr/bin/env python3
# vim: ts=2:sw=2:expandtab:autoindent

"""
format_adt.py implements pretty-printing of BAP .adt files
by translating the ADT into Python syntax, then parsing and
formatting the python.

Although this eval()s, it is made safe by using ast.literal_eval
which only supports parsing of a literal Python expression.
"""

import re
import ast
import sys
import time
import pprint
import logging
import argparse
import dataclasses
import contextlib

# grep -E "'([A-Z][a-zA-Z]+)'" src/main/antlr4/BAP_ADT.g4 --only-matching --no-filename | sort | uniq | xargs printf "'%s', " | fold -w80 -s
heads = [
  'AND', 'Annotation', 'Arg', 'Args', 'ARSHIFT', 'Attr', 'Attrs', 'BigEndian', 
  'Blk', 'Blks', 'Both', 'Call', 'Concat', 'Def', 'Defs', 'Direct', 'DIVIDE', 
  'EQ', 'Extract', 'Goto', 'HIGH', 'Imm', 'In', 'Indirect', 'Int', 'Jmp', 'Jmps', 
  'LE', 'LittleEndian', 'Load', 'LOW', 'LSHIFT', 'LT', 'Mem', 'Memmap', 'MINUS', 
  'MOD', 'NEG', 'NEQ', 'NOT', 'OR', 'Out', 'Phi', 'Phis', 'PLUS', 'Program', 
  'Project', 'Region', 'RSHIFT', 'SDIVIDE', 'Section', 'Sections', 'SIGNED', 
  'SLE', 'SLT', 'SMOD', 'Store', 'Sub', 'Subs', 'Tid', 'TIMES', 'UNSIGNED', 
  'Var', 'XOR',
]
heads_joined = '|'.join(heads)
heads_joined_b = heads_joined.encode('ascii')

log = logging.getLogger()

notspace_re = re.compile(rb'\S')
head_re = re.compile(rb'[^\s(]+')
num_re = re.compile(rb'[_0-9xa-fA-F]+')
string_re = re.compile(rb'"(?:[^"\\]|\\.)+"')

@dataclasses.dataclass
class Elem:
  begin: int
  closer: bytes
  multiline: bool

flip = {
  b'(': b')',
  b')': b'(',
  b'[': b']',
  b']': b'[',
}

def pretty(outfile, data: bytes, spaces: int):
  # stack of expression beginning parentheses and their start position
  stack: list[Elem] = []
  i = 0
  depth = 0
  head = b''

  indent = b' ' * spaces

  i0 = i - 1
  while i < len(data):
    assert i0 != i
    i0 = i

    c = bytes((data[i],))
    if c.isspace(): 
      while data[i] in b' \t\r\n':
        i += 1
    elif c.isdigit():
      m = num_re.match(data, i)
      assert m
      outfile.write(m[0])
      i = m.end(0)
    elif c == b',':
      outfile.write(b',')
      i += 1
      if stack[-1].multiline:
        outfile.write(b'\n')
        outfile.write(indent * depth)
      else:
        outfile.write(b' ')
    elif c.isupper():
      m = head_re.match(data, i)
      assert m
      i = m.end(0)
      head = m[0]
      outfile.write(head)
    elif c in b'([': 
      outfile.write(c)
      i += 1
      islist = c == b'[' and ']' != chr(data[i])
      multiline = islist or head in (b'Project', b'Def', b'Goto', b'Call', b'Sub', b'Blk', b'Arg')
      if multiline:
        depth += 1
        outfile.write(b'\n')
        outfile.write(indent * depth)

      stack.append(Elem(i, flip[c], multiline))
    elif c in b')]':
      outfile.write(c)
      i += 1

      s = stack.pop()
      assert c == s.closer
      if s.multiline:
        depth -= 1
    elif c == b'"':
      string = string_re.match(data, i)
      assert string
      outfile.write(string[0])
      i = string.end(0)
    else:
      sys.stderr.buffer.write(b'\npreceding text:\n')
      sys.stderr.buffer.write(data[max(0,i-100):i])
      raise ValueError(f"unsupported @ {i} = {c}")


@contextlib.contextmanager
def measure_time(context: str):
  log.info(f'starting {context}')
  start = time.perf_counter()
  yield lambda: time.perf_counter() - start
  log.debug(f'... done in {time.perf_counter() - start:.3f} seconds')


def main(args):
  infile = args.input
  outfile = args.output
  update = args.update
  spaces = args.spaces

  with measure_time('read'):
    data = infile.read()
    infile.close()
    log.debug(f'    read {len(data):,} characters')

  if update:
    outfile = open(infile.name, 'wb')

  with measure_time('pretty'):
    out = pretty(outfile, data, spaces)

  outfile.close()

if __name__ == '__main__':
  logging.basicConfig(format='[%(asctime)s:%(name)s@%(filename)s:%(levelname)-7s]\t%(message)s')

  argp = argparse.ArgumentParser(description="pretty formats BAP ADT files.")
  argp.add_argument('input', nargs='?', type=argparse.FileType('rb'), default=sys.stdin.buffer,
                    help="input .adt file (default: stdin)")
  excl = argp.add_mutually_exclusive_group()
  excl.add_argument('output', nargs='?', type=argparse.FileType('wb'), default=sys.stdout.buffer,
                    help="output file name (default: stdout)")

  argp.add_argument('--spaces', '-s', default=1, type=int, 
                    help="indent size in spaces (default: 1)")

  excl.add_argument('--update', '-i', action='store_true',
                    help="write output back to the input file (default: false)")

  argp.add_argument('--verbose', '-v', action='count', default=0,
                    help="print logging output to stderr (default: no, repeatable)")

  args = argp.parse_args()
  
  if args.input is sys.stdin and args.update:
    argp.error('argument --update/-i: not allowed with stdin input')

  if args.verbose == 0:
    level = logging.WARN
  elif args.verbose == 1:
    level = logging.INFO
  else:
    level = logging.DEBUG
  log.setLevel(level)

  log.debug(str(args))

  with measure_time('format_adt.main'):
    main(args)

