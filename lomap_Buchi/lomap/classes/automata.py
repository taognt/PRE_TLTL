#! /usr/bin/python

# Copyright (C) 2012-2015, Alphan Ulusoy (alphan@bu.edu)
#               2015-2017, Cristian-Ioan Vasile (cvasile@mit.edu)
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

import re
import subprocess as sp
import shlex
import operator as op
import logging
from copy import deepcopy
from collections import deque, defaultdict

import networkx as nx

from lomap.classes.model import Model
from functools import reduce

# Logger configuration
logger = logging.getLogger(__name__)
#logger.addHandler(logging.NullHandler())

'''
These variables define to which encoding the outputs of these programs
are converted to.
The SPOT encoding is for ltl2ba and ltl2fsa
The ltl2dstar encoding is for ltl2dstar
'''
spot_output_encoding = "utf-8"
ltl2dstar_output_encoding = "utf-8"

ltl2ba = "ltl2tgba -B -s -f '{formula}'"
ltl2fsa = "ltl2tgba -B -D -s -f '{formula}'"
ltl2filt = "ltlfilt -f '{formula}' --lbt"
ltl2rabin = '''ltl2dstar --ltl2nba="spin:ltl2tgba@-B -D -s" --stutter=no --output-format=native - -'''


class Automaton(Model):
    """
    Base class for deterministic or non-deterministic automata.
    """

    yaml_tag = u'!Automaton'

    def __init__(self, name= 'Unnamed automaton', props=None, multi=True):
        """
        LOMAP Automaton object constructor
        """
        Model.__init__(self, name=name, directed=True, multi=multi)

        if type(props) is dict:
            self.props = dict(props)
        else:
            self.props = list(props) if props is not None else []
            # Form the bitmap dictionary of each proposition
            # Note: range goes upto rhs-1
            self.props = dict(zip(self.props,
                                  [2 ** x for x in range(len(self.props))]))

        # Alphabet is the power set of propositions, where each element
        # is a symbol that corresponds to a tuple of propositions
        # Note: range goes upto rhs-1
        self.alphabet = set(range(0, 2 ** len(self.props)))

    def __repr__(self):
        return '''
Name: {name}
Directed: {directed}
Multi: {multi}
Props: {props}
Alphabet: {alphabet}
Initial: {init}
Final: {final}
Nodes: {nodes}
Edges: {edges}
        '''.format(name=self.name, directed=self.directed, multi=self.multi,
                   props=self.props, alphabet=self.alphabet,
                   init=list(self.init.keys()), final=self.final,
                   nodes=self.g.nodes(data=True),
                   edges=self.g.edges(data=True))

    def clone(self):
        ret = Automaton(self.name, self.props, self.multi)
        ret.g = self.g.copy()
        ret.init = dict(self.init) #FIXME: why is init a dict?
        ret.final = set(self.final)
        return ret

    def from_formula(self, formula):
        """
        Creates an automaton in-place from the given LTL formula.
        """
        raise NotImplementedError

    def get_guard_bitmap(self, guard):
        """
        Creates the bitmaps from guard string. The guard is a boolean expression
        over the atomic propositions.
        """
        # Get sets for all props
        for key in self.props:
            guard = re.sub(r'\b{}\b'.format(key),
                           "self.symbols_w_prop('{}')".format(key),
                           guard)

        # Handle (1)
        guard = re.sub(r'\(1\)', 'self.alphabet', guard)
        # Handle (0)
        guard = re.sub(r'\(0\)', 'set()', guard)

        # Handler negated sets #FIXME: this might not work in the future.
        guard = re.sub('!self.symbols_w_prop', 'self.symbols_wo_prop', guard)
        guard = re.sub('!\(self.symbols_w_prop', '(self.symbols_wo_prop', guard)

        # Convert logic connectives
        guard = re.sub(r'\&\&', '&', guard)
        guard = re.sub(r'\|\|', '|', guard)

        return eval(guard)

    def guard_from_bitmaps(self, bitmaps):
        """
        Creates a the guard Boolean formula as a string from the bitmap.
        """
        return '' #TODO: implement

    def symbols_w_prop(self, prop):
        """
        Returns symbols from the automaton's alphabet which contain the given
        atomic proposition.
        """
        bitmap = self.props[prop]
        return set([symbol for symbol in self.alphabet if bitmap & symbol])

    def symbols_wo_prop(self, prop):
        """
        Returns symbols from the automaton's alphabet which does not contain the
        given atomic proposition.
        """
        return self.alphabet.difference(self.symbols_w_prop(prop))

    def bitmap_of_props(self, props):
        """
        Returns bitmap corresponding the set of atomic propositions.
        """
        return reduce(op.or_, [self.props.get(p, 0) for p in props], 0)

    def next_states(self, q, props):
        """
        Returns the next states of state q given input proposition set props.
        """
        # Get the bitmap representation of props
        prop_bitmap = self.bitmap_of_props(props)
        # Return an array of next states
        return [v for _, v, d in self.g.out_edges_iter(q, data=True)
                                                   if prop_bitmap in d['input']]

    def next_state(self, q, props):
        """
        Returns the next state of state q given input proposition set props.

        Note: This method should only be used with deterministic automata. It
        might raise an assertion error otherwise.
        """
        # Get the bitmap representation of props
        prop_bitmap = self.bitmap_of_props(props)
        # Return an array of next states
        nq = [v for _, v, d in self.g.out_edges_iter(q, data=True)
                                                   if prop_bitmap in d['input']]
        assert len(nq) <= 1
        if nq:
            return nq[0]
        return None # This is reached only for blocking automata

    def word_from_trajectory(self, trajectory):
        '''
        Constructs an input word that induces the given finite trajectory given
        the start state, i.e., the first state of the trajectory.

        Parameters
        ----------
        trajectory : iterable
            The state trajectory.

        Returns
        -------
        word : list of symbols
            A word that induces the state trajectory
        '''
        word = []
        for state, next_state in zip(trajectory, trajectory[1:]):
            symbol = next(iter(self.g[state][next_state]['input']))
            symbol = set([prop for prop, enc in self.props.items()
                          if enc & symbol])
            word.append(symbol)
        return word

    def is_deterministic(self, check_initial=True):
        '''
        Check whether the automaton is deterministic.

        Parameters
        ----------
        check_initial : bool
            Indicates whether to check that the automaton has a single initial
            state.

        Returns
        -------
        is_deterministic : bool
        '''
        if check_initial and len(self.init) > 1:
            return False
        for state in self.g:
            for symbol in self.alphabet:
                next_states = [v for v in self.g[state]
                               if symbol in self.g[state][v]['input']]
                if len(next_states) > 1:
                    return False
        return True

    def add_trap_state(self):
        """
        Adds a trap state and completes the automaton. Returns True whenever a
        trap state has been added to the automaton.
        """
        trap_added = False
        for s in self.g:
            rem_alphabet = set(self.alphabet)
            for _, _, d in self.g.out_edges_iter(s, data=True):
                rem_alphabet -= d['input']
            if rem_alphabet:
                if not trap_added: #'trap' not in self.g:
                    self.g.add_node('trap')
                    attr_dict = {'weight': 0, 'input': self.alphabet,
                                 'guard': '(1)', 'label': '(1)'}
                    self.g.add_edge('trap', 'trap', **attr_dict)
                    trap_added = True
                attr_dict = {'weight': 0, 'input': rem_alphabet,
                             'guard': 'trap_guard', 'label': 'trap_guard'}
                self.g.add_edge(s, 'trap', **attr_dict)

        if not trap_added:
            logger.info('No trap states were added.')
        else:
            logger.info('Trap states were added.')
        return trap_added

    def remove_trap_states(self):
        '''TODO:
        '''
        raise NotImplementedError

    def prune(self):
        """TODO:

        Note: Does not update the final data structure, because it is dependent
        on the automaton type.
        """
        # set of allowed symbols, i.e. singletons and emptyset
        symbols = set([0] + list(self.props.values()))
        # update transitions and mark for deletion
        del_transitions = deque()
        for u, v, d in self.g.edges_iter(data=True):
            sym = d['input'] & symbols
            if sym:
                d['input'] = sym
            else:
                del_transitions.append((u, v))
        self.g.remove_edges_from(del_transitions)
        # delete states unreachable from the initial state
        init = next(iter(self.init.keys()))
        reachable_states = list(nx.shortest_path_length(self.g, source=init).keys())
        del_states = [n for n in self.g.nodes_iter() if n not in reachable_states]
        self.g.remove_nodes_from(del_states)
        return del_states, del_transitions



#this is a Buchi deterministic automata
class Fsa(Automaton):
    """
    Base class for (non-)deterministic finite state automata.
    """

    yaml_tag = u'!Fsa'

    def __init__(self, name='FSA', props=None, multi=True):
        """
        LOMAP Fsa Automaton object constructor
        """
        Automaton.__init__(self, name=name, props=props, multi=multi)

    def clone(self):
        ret = Fsa(self.name, self.props, self.multi)
        ret.g = self.g.copy()
        ret.init = dict(self.init) #FIXME: why is init a dict?
        ret.final = set(self.final)
        return ret

    def from_formula(self, formula, load=False):
        """
        Creates a finite state automaton in-place from the given scLTL formula.
        """
        # TODO: check that formula is syntactically co-safe
        try: # Execute ltl2tgba and get output
            lines = sp.check_output(shlex.split(ltl2fsa.format(formula=formula))).decode(spot_output_encoding)
        except Exception as ex:
            raise Exception(__name__, "Problem running ltl2tgba: '{}'".format(ex))
        automaton_from_spin(self, formula, lines)
        # We expect a deterministic FSA
        assert(len(self.init)==1)

    def is_language_empty(self):
        """
        Checks whether the FSA's language in empty.
        """
        return not any(bool(set(nx.shortest_path(self.g, state)) & self.final)
                       for state in self.init)

    def is_word_accepted(self, word, states=None, return_blocking=False):
        """
        Checks whether the input word is accepted by the FSA.

        Parameters
        ----------
        word : iterable
            Finite input word over symbols from the alphabet
        states : hashable
            State to start accepting the word from. If the states are `None`,
            the initial states of the automaton are used.
        return_blocking : bool (default: False)
            If True, returns blocking states and symbol pair.

        Returns
        -------
        is_accepted: bool
            Boolean value indicating whether the input word was accepted.
        (states, symbol) : pair of states and symbol (optional)
            The blocking states and symbol pair.

        Raises
        ------
        AssertionError
            If `state` is not a node of the automaton graph.
        """
        if states is None:
            states = self.init
        assert all(state in self.g for state in states)

        for symbol in word:
            next_states = set.union(*[set(self.next_states(state, symbol))
                                     for state in states])
            if not next_states:
                if return_blocking:
                    return False, (states, symbol)
                return False
            states = next_states
        return bool(states & self.final)

    def remove_trap_states(self):
        '''
        Removes all states of the automaton which do not reach a final state.
        Returns True whenever trap states have been removed from the automaton.
        '''
        # add virtual state which has incoming edges from all final states
        self.g.add_edges_from([(state, 'virtual') for state in self.final])
        # compute trap states
        trap_states = set(self.g.nodes_iter())
        trap_states -= set(nx.shortest_path_length(self.g, target='virtual'))
        # remove trap state and virtual state
        self.g.remove_nodes_from(trap_states | set(['virtual']))
        return len(trap_states - set(['virtual'])) == 0

    def determinize(self):
        """
        Returns a deterministic version of the Buchi automaton.
        See page 157 of [1] or [2].


        [1] Christel Baier and Joost-Pieter Katoen. Principles of Model
        Checking. MIT Press, Cambridge, Massachusetts. 2008.
        [2]  John E. Hopcroft, Rajeev Motwani, Jeffrey D. Ullman. Introduction
        to Automata Theory, Languages, and Computation. Pearson. 2006.
        """
        # Powerset construction

        # The new deterministic automaton
        det = Fsa()

        # List of state sets
        state_map = []

        # New initial state
        state_map.append(set(self.init))
        det.init[0] = 1

        # Copy the old alphabet
        det.alphabet = set(self.alphabet)

        # Copy the old props
        det.props = dict(self.props)

        # Discover states and transitions
        stack = [0]
        done = set()
        while stack:
            cur_state_i = stack.pop()
            cur_state_set = state_map[cur_state_i]
            next_states = dict()
            for cur_state in cur_state_set:
                for _,next_state,data in self.g.out_edges_iter(cur_state, True):
                    inp = next(iter(data['input']))
                    if inp not in next_states:
                        next_states[inp] = set()
                    next_states[inp].add(next_state)

            for inp,next_state_set in next_states.items():
                if next_state_set not in state_map:
                    state_map.append(next_state_set)
                next_state_i = state_map.index(next_state_set)
                attr_dict = {'weight':0, 'label':inp, 'input':set([inp])}
                det.g.add_edge(cur_state_i, next_state_i, **attr_dict)
                if next_state_i not in done:
                    stack.append(next_state_i)
                    done.add(next_state_i)

        # Sanity check
        # All edges of all states must be deterministic
        for state in det.g:
            ins = set()
            for _, _, d in det.g.out_edges_iter(state, True):
                assert len(d['input']) == 1
                inp = next(iter(d['input']))
                if inp in ins:
                    assert False
                ins.add(inp)

        # Mark final states
        for state_i, state_set in enumerate(state_map):
            if state_set & self.final:
                det.final.add(state_i)

        return det


def automaton_from_spin(aut, formula, lines):
    '''TODO:
    '''
    lines = [x.strip() for x in lines.splitlines()]

    # Get the set of propositions
    # Replace operators [], <>, X, !, (, ), &&, ||, U, ->, <-> G, F, X, R, V
    # with white-space
    props = re.sub(r'[\[\]<>X!\(\)\-&|UGFRV]', ' ', formula)
    # Replace true and false with white space
    props = re.sub(r'\btrue\b', ' ', props)
    props = re.sub(r'\bfalse\b', ' ', props)
    # What remains are propositions separated by whitespaces
    props = set(props.strip().split())

    # Form the bitmap dictionary of each proposition
    # Note: range goes upto rhs-1
    aut.props = dict(zip(props, [2 ** x for x in range(len(props))]))
    aut.name = '{} corresponding to the formula: {}'.format(aut.name, formula)
    aut.final = set()
    aut.init = {}

    # Alphabet is the power set of propositions, where each element
    # is a symbol that corresponds to a tuple of propositions
    # Note: range goes upto rhs-1
    aut.alphabet = set(range(0, 2 ** len(aut.props)))

    # Remove 'never' first line and '}' last line
    del lines[0]
    del lines[-1]

    # remove 'if', 'fi;' lines
    lines = [x for x in lines if x != 'if' and x != 'fi;']

    # '::.*' means transition, '.*:' means state
    this_state = None
    for line in lines:
        if(line[0:2] == '::'):
            m = re.search(':: (.*) -> goto (.*)', line)
            guard = m.group(1)
            bitmaps = aut.get_guard_bitmap(guard)
            next_state = m.group(2)
            # Add edge
            transition_data = {'weight': 0, 'input': bitmaps,
                               'guard' : guard, 'label': guard}
            aut.g.add_edge(this_state, next_state, attr_dict=transition_data)
        elif line[0:4] == 'skip':
            # Add self-looping edge
            transition_data = {'weight': 0, 'input': aut.alphabet,
                               'guard' : '(1)', 'label': '(1)'}
            aut.g.add_edge(this_state, this_state, attr_dict=transition_data)
        else:
            this_state = line[0:-1]
            # Add state
            aut.g.add_node(this_state)
            # Mark final or init
            if this_state.endswith('init'):
                aut.init[this_state] = 1
            if this_state.startswith('accept'):
                aut.final.add(this_state)

def infix_formula_to_prefix(formula):
    # This function expects a string where operators and parantheses
    # are separated by single spaces, props are lower-case.
    #
    # Tokenizes and reverses the input string.
    # Then, applies the infix to postfix algorithm.
    # Finally, reverses the output string to obtain the prefix string.
    #
    # Infix to postfix algorithm is taken from:
    # http://www.cs.nyu.edu/courses/fall09/V22.0102-002/lectures/
    # InfixToPostfixExamples.pdf
    # http://www.programmersheaven.com/2/Art_Expressions_p1
    #
    # Operator priorities are taken from:
    # Principles of Model Checking by Baier, pg.232
    # http://www.voronkov.com/lics_doc.cgi?what=chapter&n=14
    # Logic in Computer Science by Huth and Ryan, pg.177

    # Operator priorities (higher number means higher priority)
    operators = {"I": 0, "|" : 1, "&": 1, "U": 2, "G": 3, "F": 3, "X": 3,
                 "!": 3}
    output = []
    stack = []

    # Remove leading, trailing, multiple white-space, and
    # split string at whitespaces
    formula = re.sub(r'\s+',' ',formula).strip().split()

    # Reverse the input
    formula.reverse()

    # Invert the parantheses
    for i in range(0,len(formula)):
        if formula[i] == '(':
            formula[i] = ')'
        elif formula[i] == ')':
            formula[i] = '('

    # Infix to postfix conversion
    for entry in formula:

        if entry == ')':
            # Closing paranthesis: Pop from stack until matching '('
            popped = stack.pop()
            while stack and popped != '(':
                output.append(popped)
                popped = stack.pop()

        elif entry == '(':
            # Opening paranthesis: Push to stack
            # '(' has the highest precedence when in the input
            stack.append(entry)

        elif entry not in operators:
            # Entry is an operand: append to output
            output.append(entry)

        else:
            # Operator: Push to stack appropriately
            while True:
                if not stack or stack[-1] == '(':
                    # Push to stack if empty or top is '('
                    # '(' has the lowest precedence when in the stack
                    stack.append(entry)
                    break
                elif operators[stack[-1]] < operators[entry]:
                    # Push to stack if prio of top of the stack
                    # is lower than the current entry
                    stack.append(entry)
                    break
                else:
                    # Pop from stack and try again
                    popped = stack.pop()
                    output.append(popped)

    # Pop remaining entries from the stack
    while stack:
        popped = stack.pop()
        output.append(popped)

    # Reverse the order and join entries w/ space
    output.reverse()
    formula = ' '.join(output)

    return formula
