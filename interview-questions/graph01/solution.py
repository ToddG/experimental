#!/usr/bin/env python3
from enum import Enum
from operator import itemgetter
import pdb
import sys
import logging

logger = logging.getLogger('solution')

class Node:
    """
    Reference parents and children by name.

    >>> n = Node("foo")
    >>> n
    foo
    >>> n.is_system = True
    >>> n
    [*]foo
    """
    def __init__(self, name: str):
        self._name = name
        self._parents = set()
        self._children = set()
        self.is_system = False

    @property
    def name(self):
        return self._name

    @property
    def parents(self):
        return self._parents
    
    @property
    def children(self):
        return self._children

    def add_parent(self, parent):
        self._parents.add(parent)

    def add_child(self, child):
        self._children.add(child)

    def remove_parent(self, parent):
        self._parents.remove(parent)

    def remove_child(self, child):
        self._children.remove(child)

    def __repr__(self):
        if self.is_system:
            return "[*]%s" % self.name
        else:
            return self.name


class Graph:
    """
    >>> g = Graph()
    """
    def __init__(self):
        # maintaining the roots enables printing out the graph
        self._roots = set() #str -- list of node keys
        # all nodes are here
        self._nodes = {}    #key: str, val: Node

    def add_node(self, node:Node):
        if node.name in self._nodes.keys() or node.name in self._roots:
            logger.warning("Cannot add node. Node already exists: %s" % node)
            return
        self._nodes[node.name] = node
        self._roots.add(node.name)

    def make_dep(self, parentkey:str, childkey:str):
        if parentkey not in self._nodes.keys():
            logger.warning("Error: cannot add node dependency. Parent node key ['%s'] not found in graph." % parentkey)
            return
        if childkey not in self._nodes.keys():
            logger.warning("Error: cannot add node dependency. Child node key ['%s'] not found in graph." % childkey)
            return
        parentnode = self._nodes[parentkey]
        if childkey in self._roots:
            self._roots.remove(childkey)
        childnode = self._nodes[childkey]
        childnode.add_parent(parentkey)
        parentnode.add_child(childkey)

    def remove(self, nodekey:str):
        if nodekey not in self._nodes.keys():
            logger.warning("Error: cannot remove node. Node key ['%s'] not found in graph." % nodekey)
            return
        node = self._nodes[nodekey]
        if node.is_system:
            logger.warning("Error: cannot remove node. Node ['%s'] is a system node, these are not removable." % nodekey)
            return
        if len(node.parents) != 0:
            logger.warning("Error: cannot remove node. Node ['%s'] is dependent on by : %s." % (nodekey, node.parents))
            return
        # remove this node and remove it from the parents of child nodes, transitively removing them if they have no other parents
        for childkey in node.children:
            self.unparent(nodekey, childkey)
        self._nodes.pop(nodekey)
        if nodekey in self._roots:
            self._roots.remove(nodekey)

    def unparent(self, parentkey: str, nodekey:str):
        node = self._nodes[nodekey]
        node.remove_parent(parentkey)
        if len(node.parents) == 0:
            self._roots.add(nodekey)
            if not node.is_system:
                self.remove(nodekey)
       
    def make_system(self, nodekey:str):
        if nodekey not in self._nodes.keys():
            logger.warning("Error: cannot remove node. Node key ['%s'] not found in graph." % nodekey)
            return
        self._nodes[nodekey].is_system = True

    def reify(self, key: str):
        n = self._nodes[key]
        m = {'name':str(n), 'children':sorted([self.reify(c) for c in n.children], key=itemgetter('name'))}
        return m

    def __repr__(self):
        return str(sorted([self.reify(r) for r in sorted(self._roots)], key=itemgetter('name')))


class Command(Enum):
    """
    Parser lexicon includes the following commands.
    Commands not in this lexicon are ignored.
    """
    ADD = 1
    DEP = 2
    REMOVE = 3
    SYSTEM = 4
    PRINT = 5

class FileReader:
    """
    Reads input file
    """
    
    def __init__(self, args):
        self._file = args.file

    def lines(self):
        with open(self._file, 'r') as f:
            return f.readlines()

class FakeReader(FileReader):
    def __init__(self, lines):
        self._lines = lines

    def lines(self):
        return self._lines

class CommandParser:
    """
    Commands : ADD DEP REMOVE SYSTEM PRINT

    # Tests

    ## Test 01
    ADD a b c

    >>> fake_reader = FakeReader(["ADD a b c", "PRINT"])
    >>> CommandParser(fake_reader).parse()
    [{'name': 'a', 'children': []}, {'name': 'b', 'children': []}, {'name': 'c', 'children': []}]

    ## Test 02
    ADD a b c

    >>> fake_reader = FakeReader(["ADD a b c", "PRINT"])
    >>> CommandParser(fake_reader).parse()
    [{'name': 'a', 'children': []}, {'name': 'b', 'children': []}, {'name': 'c', 'children': []}]

    """
    def __init__(self, reader: FileReader):
        self._reader = reader
        self._graph = Graph()

    def parse(self):
        for line in self._reader.lines():
            logger.debug(line)
            parts = line.split(" ")
            command = parts[0]
            args = parts[1:]
            if Command.ADD.name == command:
                self.do_add(args)
            elif Command.DEP.name == command:
                self.do_dep(args)
            elif Command.REMOVE.name == command:
                self.do_remove(args)
            elif Command.SYSTEM.name == command:
                self.do_system(args)
            elif Command.PRINT.name == command:
                self.do_print(args)
            else:
                raise Exception("Unknown command: %s" % command)


    def do_add(self, args):
        """
        ADD a b c

        >>> fake_reader = FakeReader([""])
        >>> p = CommandParser(fake_reader)
        >>> p.do_add(['a', 'b', 'c'])
        >>> p._graph
        [{'name': 'a', 'children': []}, {'name': 'b', 'children': []}, {'name': 'c', 'children': []}]

        >>> fake_reader = FakeReader(["ADD a b c"])
        >>> CommandParser(fake_reader).parse()


        >>> fake_reader = FakeReader(["ADD a b c", "PRINT"])
        >>> CommandParser(fake_reader).parse()
        [{'name': 'a', 'children': []}, {'name': 'b', 'children': []}, {'name': 'c', 'children': []}]
        """
        nodes = [Node(x) for x in args]
        for node in nodes:
            self._graph.add_node(node)
        
    def do_dep(self, args):
        """
        ADD a b c
        DEP a b 
        DEP b c

        >>> fake_reader = FakeReader([""])
        >>> p = CommandParser(fake_reader)
        >>> p.do_add(['a', 'b', 'c'])
        >>> p.do_dep(['a', 'b'])
        >>> p.do_dep(['b', 'c'])
        >>> p._graph
        [{'name': 'a', 'children': [{'name': 'b', 'children': [{'name': 'c', 'children': []}]}]}]

        >>> fake_reader = FakeReader(["ADD a b c", "DEP a b", "DEP b c", "PRINT"])
        >>> CommandParser(fake_reader).parse()
        [{'name': 'a', 'children': [{'name': 'b', 'children': [{'name': 'c', 'children': []}]}]}]
        """
        parentkey = args[0]
        depkeys = args[1:]
        for depkey in depkeys:
            self._graph.make_dep(parentkey, depkey)
    
    def do_remove(self, args):
        """
        ADD a b c
        DEP a b 
        DEP b c
        REMOVE a

        >>> p = CommandParser(FakeReader([""]))
        >>> p.do_add(['a', 'b', 'c'])
        >>> p.do_dep(['a', 'b'])
        >>> p.do_dep(['b', 'c'])
        >>> p.do_remove(['a'])
        >>> p._graph
        []

        >>> CommandParser(FakeReader(["ADD a b c", "DEP a b", "DEP b c", "REMOVE a", "PRINT"])).parse()
        []

        ADD a b c
        DEP a b 
        DEP b c
        REMOVE c

        >>> CommandParser(FakeReader(["ADD a b c", "DEP a b", "DEP b c", "REMOVE c", "PRINT"])).parse()
        [{'name': 'a', 'children': [{'name': 'b', 'children': [{'name': 'c', 'children': []}]}]}]
        """
        depkeys = args[:]
        for depkey in depkeys:
            self._graph.remove(depkey)

    def do_system(self, args):
        """
        ADD a
        SYSTEM a
        REMOVE a
        PRINT

        >>> CommandParser(FakeReader(["ADD a", "SYSTEM a", "REMOVE a", "PRINT"])).parse()
        [{'name': '[*]a', 'children': []}]

        ADD a b c
        DEP a b 
        DEP b c
        SYSTEM b
        REMOVE a

        >>> CommandParser(FakeReader(["ADD a b c", "DEP a b", "DEP b c", "SYSTEM b", "REMOVE a", "PRINT"])).parse()
        [{'name': '[*]b', 'children': [{'name': 'c', 'children': []}]}]
       """
        depkeys = args[:]
        for depkey in depkeys:
            self._graph.make_system(depkey)

    def do_print(self, args):
        print(self._graph)


if __name__ == "__main__":

    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("file", help="input file name")
    parser.add_argument("-d", "--debug", help="increase output verbosity", action="store_true")
    parser.add_argument("-s", "--skiptests", help="skip internal doctests", action="store_true")
    args = parser.parse_args()

    if args.debug == True:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.ERROR)

    if args.skiptests == True:
        print("skipping doc tests...")
    else:
        import doctest
        doctest.testmod()
        print ("doc tests complete")

    CommandParser(FileReader(args)).parse()
