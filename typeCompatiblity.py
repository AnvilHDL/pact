from dataclasses import dataclass
import os
from typing import List, Set, Tuple, Optional, Dict
from enum import Enum
import sys
import traceback
from PIL import Image

PWD = os.path.dirname(os.path.abspath(__file__))
global debug_mode
debug_mode = False
class TypeKind(Enum):
    END = "end"
    DELAY = "delay"
    ACTION = "action"
    BLOCKING_ACTION = "blocking_action"
    FUTURE = "future"
    SEQUENCE = "sequence"
    PARALLEL = "parallel"
    INTERNAL_CHOICE = "internal_choice"  # + operator
    EXTERNAL_CHOICE = "external_choice"  # & operator - offering choice (can take multiple if all offered)
    EXCLUSIVE_CHOICE = "exclusive_choice"  # ^ operator - exclusive choice (pick exactly one)

@dataclass
class SessionType:
    kind: TypeKind
    label: Optional[str] = None
    first: Optional['SessionType'] = None
    second: Optional['SessionType'] = None
    options: Optional[List['SessionType']] = None
    branches: Optional[List[Tuple[str, 'SessionType']]] = None

class Parser:
    def __init__(self, input_str: str):
        self.input = input_str.strip()
        self.pos = 0
    
    def parse(self) -> SessionType:
        if self.input == '#':
            return SessionType(TypeKind.DELAY)
        elif self.input == 'end':
            return SessionType(TypeKind.END)
        return self.parse_choice()
    
    def parse_choice(self) -> SessionType:
        left = self.parse_exclusive_choice()
        if self.peek('+'):
            self.consume('+')
            options = [left]
            while True:
                options.append(self.parse_exclusive_choice())
                if not self.peek('+'):
                    break
                self.consume('+')
            return SessionType(TypeKind.INTERNAL_CHOICE, options=options)
        return left
    
    def parse_exclusive_choice(self) -> SessionType:
        left = self.parse_parallel()
        if self.peek('^'):
            self.consume('^')
            right = self.parse_parallel()
            # For now, model as branches with labels from the actions
            # This is a simplified version - proper implementation would extract labels
            return SessionType(TypeKind.EXCLUSIVE_CHOICE, first=left, second=right)
        return left
    
    def parse_parallel(self) -> SessionType:
        left = self.parse_sequence()
        if self.peek('||'):
            self.consume('||')
            right = self.parse_sequence()
            return SessionType(TypeKind.PARALLEL, first=left, second=right)
        return left
    
    def parse_sequence(self) -> SessionType:
        left = self.parse_external_choice()
        if self.peek(';'):
            self.consume(';')
            right = self.parse_sequence()
            return SessionType(TypeKind.SEQUENCE, first=left, second=right)
        return left
    
    def parse_external_choice(self) -> SessionType:
        # Check for a:t & b:t pattern (offering choice - can accept multiple if all offered)
        saved_pos = self.pos
        try:
            branches = []
            while True:
                label = self.parse_atom()
                if isinstance(label, SessionType) and (label.kind == TypeKind.ACTION or label.kind == TypeKind.BLOCKING_ACTION):
                    label_str = label.label
                else:
                    self.pos = saved_pos
                    return self.parse_primary()
                
                if self.peek(':'):
                    self.consume(':')
                    cont = self.parse_primary()
                    branches.append((label_str, cont))
                else:
                    branches.append((label_str, SessionType(TypeKind.END)))
                
                if not self.peek('&') and not self.peek('^'):
                    break
                
                # Determine if this is & (offering) or ^ (exclusive)
                is_exclusive = self.peek('^')
                self.consume('^' if is_exclusive else '&')
                
                # If we see ^, mark all branches as exclusive choice
                if is_exclusive:
                    # Read remaining branches
                    while True:
                        label = self.parse_atom()
                        if isinstance(label, SessionType) and (label.kind == TypeKind.ACTION or label.kind == TypeKind.BLOCKING_ACTION):
                            label_str = label.label
                        else:
                            break
                        
                        if self.peek(':'):
                            self.consume(':')
                            cont = self.parse_primary()
                            branches.append((label_str, cont))
                        else:
                            branches.append((label_str, SessionType(TypeKind.END)))
                        
                        if not self.peek('^'):
                            break
                        self.consume('^')
                    
                    if len(branches) > 1:
                        return SessionType(TypeKind.EXCLUSIVE_CHOICE, branches=branches)
                    break
            
            if len(branches) > 1:
                return SessionType(TypeKind.EXTERNAL_CHOICE, branches=branches)
            elif len(branches) == 1:
                # Single branch - just return it directly if it's just the action
                # (This handles simple actions like "m1" or "B_m1" without continuation)
                label_str, cont = branches[0]
                if cont.kind == TypeKind.END:
                    # No continuation, just return to primary parsing
                    self.pos = saved_pos
                    return self.parse_primary()
                else:
                    # Has continuation, create sequence
                    # Determine if action is blocking by checking for B_ prefix
                    is_blocking_action = label_str.startswith('B_')
                    return SessionType(TypeKind.SEQUENCE, 
                                     first=SessionType(TypeKind.BLOCKING_ACTION if is_blocking_action else TypeKind.ACTION, 
                                                     label=label_str),
                                     second=cont)
        except:
            self.pos = saved_pos
        
        return self.parse_primary()
    
    def parse_primary(self) -> SessionType:
        self.skip_whitespace()
        
        # Future operator
        if self.peek('F ') or self.peek('F('):
            self.consume('F')
            self.skip_whitespace()
            inner = self.parse_primary()
            return SessionType(TypeKind.FUTURE, first=inner)
        
        # Parentheses
        if self.peek('('):
            self.consume('(')
            result = self.parse()
            self.consume(')')
            return result
        
        return self.parse_atom()
    
    def parse_atom(self) -> SessionType:
        self.skip_whitespace()
        label = ""
        while self.pos < len(self.input) and self.input[self.pos] not in [';', '&', '|', '+', '^', ':', '(', ')', ' ', ',']:
            label += self.input[self.pos]
            self.pos += 1
        
        if not label:
            raise ValueError(f"Expected action at position {self.pos}")
        label = label.replace(',', '').strip()
        
        # Special keywords
        if label == '#':
            return SessionType(TypeKind.DELAY)
        elif label == 'end':
            return SessionType(TypeKind.END)
        
        # Handle explicit B_ prefix for blocking actions (e.g., B_m1)
        # B_m1 means: offers both B_m1 (blocking state) and m1 (actual action)
        if label.startswith('B_'):
            # This is explicitly a blocking action with B_ prefix
            # Store the full label including B_ prefix
            return SessionType(TypeKind.BLOCKING_ACTION, label=label)
        
        # All other actions are non-blocking regular actions
        # Whether m1, M1, action_name, etc.
        return SessionType(TypeKind.ACTION, label=label)
    
    def peek(self, s: str) -> bool:
        self.skip_whitespace()
        return self.input[self.pos:self.pos+len(s)] == s
    
    def consume(self, s: str):
        self.skip_whitespace()
        if not self.peek(s):
            raise ValueError(f"Expected '{s}' at position {self.pos}")
        self.pos += len(s)
    
    def skip_whitespace(self):
        while self.pos < len(self.input) and self.input[self.pos] in [' ', '\t', '\n']:
            self.pos += 1

@dataclass 
class Transition:
    from_state: int
    to_state: int
    label: Set[str]  # Set of action labels
    is_blocking: bool = False
    is_epsilon: bool = False
    is_conditional_epsilon: bool = False # for instantaneous send or receive
    is_internal_choice: bool = False
    is_exclusive_choice: bool = False
    is_offering_choice: bool = False

@dataclass
class State:
    id: int
    accepting: bool = False

class Automaton:
    def __init__(self):
        self.states: dict[int, State] = {}
        self.transitions: List[Transition] = []
        self.initial = 0
        self.next_id = 0
        self.automaton_id = id(self)  # Unique ID for this automaton instance

    def new_state(self, accepting=False) -> int:
        sid = self.next_id
        self.next_id += 1
        self.states[sid] = State(sid, accepting)
        return sid

    def add_transition(self, from_s: int, to_s: int, labels: Set[str], is_blocking=False, is_epsilon=False, 
                      is_internal_choice=False, is_exclusive_choice=False, is_offering_choice=False, is_conditional_epsilon=False):
        # Convert single string to set if needed (for backwards compatibility)
        if isinstance(labels, str):
            labels = {labels}
        
        # Check if a transition with same from/to already exists, merge labels if so
        for existing_trans in self.transitions:
            if (existing_trans.from_state == from_s and 
                existing_trans.to_state == to_s):
                # Merge labels into existing transition
                existing_trans.label = existing_trans.label | labels
                return
        
        # No existing transition found, create new one
        trans = Transition(from_s, to_s, labels, is_blocking=is_blocking, is_epsilon=is_epsilon,
                         is_internal_choice=is_internal_choice, is_exclusive_choice=is_exclusive_choice,
                         is_offering_choice=is_offering_choice, is_conditional_epsilon=is_conditional_epsilon)
        self.transitions.append(trans)
    
    def delete_transition(self, from_s: int, to_s: int, label: str):
        trans_to_remove = None
        for trans in self.transitions:
            if trans.from_state == from_s and trans.to_state == to_s and label in trans.label:
                trans_to_remove = trans
                break
        if trans_to_remove:
            self.transitions.remove(trans_to_remove)


def label_equivalence(labels1: Set[str], labels2: Set[str]) -> bool:
    """Check if two label sets have any compatible labels"""
    labels1_satisfied = True
    labels2_satisfied = True
    for label1 in labels1:
        found = False
        for label2 in labels2:
            if check_label_satisfiability(label1, label2):
                found = True
                break
        if not found:
            labels1_satisfied = False
            break
    if not labels1_satisfied:
        return False
    else:
        for label2 in labels2:
            found = False
            for label1 in labels1:
                if check_label_satisfiability(label2, label1):
                    found = True
                    break
            if not found:
                labels2_satisfied = False
                break
        if labels2_satisfied:
            return True
        else:
            return False




'''
label satisfiablity checks
    # |-> EVERYTHING
    B_m |-> m, self, #F_m
    m |-> m, B_m,
    #_Bm |-> #,m' or B_m' for any m' other than m
    #F_Bm |-> Same as #_Bm
    #FB_m |-> B_m, self
    #F |-> Nothing
    #F_m |-> B_m
    #end |-> everything except #end
    ac |-> c
    c |-> ac
    e |-> epsilon, same state for the other one
'''

def check_label_satisfiability(label1: str, label2: str) -> bool:
    # check if label 2 satisfies label1
    
    # Choice synchronization: must match exactly
    if label1.startswith('#choice_') and label2.startswith('#choice_'):
        return label1 == label2
    
    if label1 == '#':
        return True
    elif label1.startswith('B_'):
        m1 = label1[2:]
        return label2 == m1 or label2 == label1 or label2 == '#F_' + m1 or (label2 == '#F' + label1)
    elif not label1.startswith('B_') and not label1.startswith('#'):
        return label2 == label1 or label2 == 'B_' + label1
    elif label1.startswith('#_B') or label1.startswith('#F_B') or label1.startswith('#EC::'):
        m1_sets = set()
        m1 = None
        if label1.startswith('#_B'):
            m1 = label1[3:]
        elif label1.startswith('#F_B'):
            m1 = label1[4:]
        elif label1.startswith('#EC::'):
            m1 = label1[5:]  # Skip '#EC::'
            m1_sets = set(m1.split('::'))
            if label2 == '#c':
                return True

        if label2 == '#':
            return True
        elif label2.startswith('B_'):
            m2 = label2[2:]
            if label1.startswith('#EC::'):
                return ('Bm' + m2) not in m1_sets
            return m1 != m2
        elif not label2.startswith('B_') and not label2.startswith('#'):
            if label1.startswith('#EC::'):
                return ('Bm' + label2) not in m1_sets
            return m1 != label2
        else:
            return False
    elif label1.startswith('#FB_'):
        return label2 == label1 or label2 == label1[2:]
    elif label1 == '#F':
        return False
    elif label1.startswith('#F_'):
        m1 = label1[3:]
        return label2 == 'B_' + m1
    elif label1 == '#end':
        return label2 != '#end'
    elif label1 == '#c':
        # Internal choice token: only satisfiable by external choice token
        return (label2.startswith('#ac')) or (label2.startswith('#EC::'))
    elif label1.startswith('#ac'):
        # External choice token: only satisfiable by internal choice token
        return label2 == '#c'
    else:
        raise ValueError(f"Unknown label format: {label1}")
    
def create_product_automaton(auto1: Automaton, auto2: Automaton) -> Tuple[Automaton, bool, str]:
    product_auto = Automaton()
    state_map: Dict[Tuple[int, int], int] = {}

    def get_state_id(s1: int, s2: int) -> int:
        if (s1, s2) not in state_map:
            state_map[(s1, s2)] = product_auto.new_state()
        return state_map[(s1, s2)]
    initial_product_state = get_state_id(auto1.initial, auto2.initial)
    product_auto.initial = initial_product_state
    
    # Build product automaton transitions
    worklist = [(auto1.initial, auto2.initial)]
    visited = set()
    
    while worklist:
        s1, s2 = worklist.pop()
        if (s1, s2) in visited:
            continue
        visited.add((s1, s2))
        
        ps = get_state_id(s1, s2)
        accepting = auto1.states[s1].accepting and auto2.states[s2].accepting
        trans1 = [t for t in auto1.transitions if t.from_state == s1]
        trans2 = [t for t in auto2.transitions if t.from_state == s2]
        accepting = auto1.states[s1].accepting and auto2.states[s2].accepting

        def find_matching_transitions(trans1, trans2):
            found = False
            # Simple matching - choice synchronization is now in the labels!
            for t1 in trans1:
                for t2 in trans2:
                    if label_equivalence(t1.label, t2.label):
                        found = True
                        to_product_state = get_state_id(t1.to_state, t2.to_state)
                        combined_labels = t1.label | t2.label
                        product_auto.add_transition(ps, to_product_state, combined_labels,
                                                is_blocking=t1.is_blocking or t2.is_blocking,
                                                is_epsilon=t1.is_epsilon and t2.is_epsilon,
                                                is_internal_choice=t1.is_internal_choice or t2.is_internal_choice,
                                                is_exclusive_choice=t1.is_exclusive_choice or t2.is_exclusive_choice,
                                                is_offering_choice=t1.is_offering_choice or t2.is_offering_choice,
                                                is_conditional_epsilon=t1.is_conditional_epsilon or t2.is_conditional_epsilon)
                        
                        if auto1.states[t1.to_state].accepting and auto2.states[t2.to_state].accepting:
                            product_auto.states[to_product_state].accepting = True
                            product_auto.add_transition(to_product_state, to_product_state, {'#end'}, is_epsilon=False)
                        
                        worklist.append((t1.to_state, t2.to_state))
            
            return found
        found = find_matching_transitions(trans1, trans2)
        if not found:
            # Check for accepting states to allow epsilon transitions
            if not accepting and auto1.states[s1].accepting:
                trans1 = [t for t in auto1.transitions if t.from_state == auto1.initial]
                found = find_matching_transitions(trans1, trans2)
            elif not accepting and auto2.states[s2].accepting:
                trans2 = [t for t in auto2.transitions if t.from_state == auto2.initial]
                found = find_matching_transitions(trans1, trans2)

        if not found and not accepting:
            # check for epsilon transitions
            found = False
            e_trans1 = [t for t in auto1.transitions if t.from_state == s1 and t.is_epsilon]
            e_trans2 = [t for t in auto2.transitions if t.from_state == s2 and t.is_epsilon]
            if e_trans1:
                for et1 in e_trans1:
                    to_product_state = get_state_id(et1.to_state, s2)
                    product_auto.add_transition(ps, to_product_state, et1.label,
                                            is_blocking=et1.is_blocking,
                                            is_epsilon=True,
                                            is_internal_choice=et1.is_internal_choice,
                                            is_exclusive_choice=et1.is_exclusive_choice,
                                            is_offering_choice=et1.is_offering_choice,
                                            is_conditional_epsilon=et1.is_conditional_epsilon)
                    if auto1.states[et1.to_state].accepting and auto2.states[s2].accepting:
                        product_auto.states[to_product_state].accepting = True
                        product_auto.add_transition(to_product_state, to_product_state, {'#end'}, is_epsilon=False)
                    worklist.append((et1.to_state, s2))
                found = True
            if e_trans2:
                for et2 in e_trans2:
                    to_product_state = get_state_id(s1, et2.to_state)
                    product_auto.add_transition(ps, to_product_state, et2.label,
                                            is_blocking=et2.is_blocking,
                                            is_epsilon=True,
                                            is_internal_choice=et2.is_internal_choice,
                                            is_exclusive_choice=et2.is_exclusive_choice,
                                            is_offering_choice=et2.is_offering_choice,
                                            is_conditional_epsilon=et2.is_conditional_epsilon)
                    if auto1.states[s1].accepting and auto2.states[et2.to_state].accepting:
                        product_auto.states[to_product_state].accepting = True
                        product_auto.add_transition(to_product_state, to_product_state, {'#end'}, is_epsilon=False)
                    worklist.append((s1, et2.to_state))
                found = True
            if not found and not accepting:
                # check for conditional epsilon transitions
                c_trans1 = [t for t in auto1.transitions if t.from_state == s1 and  all(l.startswith('#ac') for l in t.label)]
                c_trans2 = [t for t in auto2.transitions if t.from_state == s2 and t.to_state==s2 and all(l.startswith('#_B') for l in t.label)]
                if c_trans1:
                    for et1 in c_trans1:
                        to_product_state = get_state_id(et1.to_state, s2)
                        product_auto.add_transition(ps, to_product_state, et1.label,
                                                is_blocking=et1.is_blocking,
                                                is_epsilon=True,
                                                is_internal_choice=et1.is_internal_choice,
                                                is_exclusive_choice=et1.is_exclusive_choice,
                                                is_offering_choice=et1.is_offering_choice,
                                                is_conditional_epsilon=et1.is_conditional_epsilon)
                        if auto1.states[et1.to_state].accepting and auto2.states[s2].accepting:
                            product_auto.states[to_product_state].accepting = True
                            product_auto.add_transition(to_product_state, to_product_state, {'#end'}, is_epsilon=False)
                        worklist.append((et1.to_state, s2))
                    found = True
                c_trans2 = [t for t in auto2.transitions if t.from_state == s2 and all(l.startswith('#ac') for l in t.label)]
                c_trans1 = [t for t in auto1.transitions if t.from_state == s1 and t.to_state==s1 and all(l.startswith('#_B') for l in t.label)]
                if c_trans2:
                    for et2 in c_trans2:
                        to_product_state = get_state_id(s1, et2.to_state)
                        product_auto.add_transition(ps, to_product_state, et2.label,
                                                is_blocking=et2.is_blocking,
                                                is_epsilon=True,
                                                is_internal_choice=et2.is_internal_choice,
                                                is_exclusive_choice=et2.is_exclusive_choice,
                                                is_offering_choice=et2.is_offering_choice,
                                                is_conditional_epsilon=et2.is_conditional_epsilon)
                        if auto1.states[s1].accepting and auto2.states[et2.to_state].accepting:
                            product_auto.states[to_product_state].accepting = True
                            product_auto.add_transition(to_product_state, to_product_state, {'#end'}, is_epsilon=False)
                        worklist.append((s1, et2.to_state))
                    found = True

                

            if not found:
                return None, False, f"No matching transitions for states ({s1}, {s2}) | actions for type 1 : {[t.label for t in trans1]} | actions for type 2 : {[t.label for t in trans2]}"                
    if debug_mode:
        print("Product automaton constructed.")
        print_debug(product_auto)
    # check any acceptable state is reachable
    reachable_accepting_states = [s for s in product_auto.states if product_auto.states[s].accepting]
    if not reachable_accepting_states:
        return product_auto, False, "Deadlock: No reachable accepting states in product automaton."
    else:
        return product_auto, True, "Compatible, constructed product automaton."


def print_debug(automaton: Automaton):
    print("Automaton States:")
    for sid, state in automaton.states.items():
        acc = " (accepting)" if state.accepting else ""
        print(f"  State {sid}{acc}")
    print("Automaton Transitions:")
    for trans in automaton.transitions:
        print(f"  {trans.from_state} --{trans.label}--> {trans.to_state}")


def create_choice_product_branches(auto: Automaton, left_end: int, right_end: int, current: int, 
                                   left_start: int, right_start: int, is_internal: bool = True) -> int:
    """
    Create product for choice branches.
    
    Internal choice (m1+m2): Build as m1; #c; m2 (sequence with choice token)
    External choice (m1&m2): Build with optional transitions between branches
    
    Returns the final merged state.
    """
    if is_internal:
        # Internal choice: m1; #c; m2 (both branches in sequence)
        # Get all states and transitions for left branch
        left_states = set()
        left_trans = []
        queue = [left_start]
        visited = set()
        while queue:
            s = queue.pop(0)
            if s in visited:
                continue
            visited.add(s)
            left_states.add(s)
            for t in auto.transitions:
                if t.from_state == s and t not in left_trans:
                    left_trans.append(t)
                    if t.to_state not in visited:
                        queue.append(t.to_state)
        
        # Get all states and transitions for right branch
        right_states = set()
        right_trans = []
        queue = [right_start]
        visited = set()
        while queue:
            s = queue.pop(0)
            if s in visited:
                continue
            visited.add(s)
            right_states.add(s)
            for t in auto.transitions:
                if t.from_state == s and t not in right_trans:
                    right_trans.append(t)
                    if t.to_state not in visited:
                        queue.append(t.to_state)
        
        # Rebuild from current: left branch -> #c -> right branch
        # Map left states
        left_state_map = {}
        
        def get_left_mapped_state(s):
            if s == left_start:
                return current
            if s not in left_state_map:
                left_state_map[s] = auto.new_state()
            return left_state_map[s]
        
        # Build left branch from current
        for trans in left_trans:
            from_s = get_left_mapped_state(trans.from_state)
            to_s = get_left_mapped_state(trans.to_state)
            auto.add_transition(from_s, to_s, trans.label,
                              is_blocking=trans.is_blocking,
                              is_epsilon=trans.is_epsilon,
                              is_internal_choice=trans.is_internal_choice,
                              is_exclusive_choice=trans.is_exclusive_choice,
                              is_offering_choice=trans.is_offering_choice,
                              is_conditional_epsilon=trans.is_conditional_epsilon)
        
        # Add choice synchronization token from left_end to right_start
        left_end_mapped = get_left_mapped_state(left_end)
        choice_sync_state = auto.new_state()
        # Internal choice uses #c token
        auto.add_transition(left_end_mapped, choice_sync_state, {'#c'}, is_epsilon=False)
        
        # Map right states
        right_state_map = {right_start: choice_sync_state}
        
        def get_right_mapped_state(s):
            if s not in right_state_map:
                right_state_map[s] = auto.new_state()
            return right_state_map[s]
        
        # Build right branch from choice_sync_state
        for trans in right_trans:
            from_s = get_right_mapped_state(trans.from_state)
            to_s = get_right_mapped_state(trans.to_state)
            auto.add_transition(from_s, to_s, trans.label,
                              is_blocking=trans.is_blocking,
                              is_epsilon=trans.is_epsilon,
                              is_internal_choice=trans.is_internal_choice,
                              is_exclusive_choice=trans.is_exclusive_choice,
                              is_offering_choice=trans.is_offering_choice,
                              is_conditional_epsilon=trans.is_conditional_epsilon)
        
        final = get_right_mapped_state(right_end)
        
        # Delete original branch transitions and states
        for trans in left_trans + right_trans:
            if trans in auto.transitions:
                auto.transitions.remove(trans)
        
        states_to_delete = (left_states | right_states) - {current}
        for state_id in states_to_delete:
            if state_id in auto.states:
                del auto.states[state_id]
        return final


def create_async_product_branches(auto: Automaton, left_end: int, right_end: int, current: int, left_start: int, right_start: int) -> int:
    """
    Synchronous product for parallel branches (s1 || s2).
    Both branches must step together - picks one transition from each branch and merges labels.
    BUT: self-loops can happen independently (for blocking actions).
    
    Returns the final merged state.
    """
    # Get all states for each branch
    def get_branch_states(start):
        states = set()
        queue = [start]
        visited = set()
        while queue:
            s = queue.pop(0)
            if s in visited:
                continue
            visited.add(s)
            states.add(s)
            for t in auto.transitions:
                if t.from_state == s and t.to_state not in visited:
                    queue.append(t.to_state)
        return states
    
    left_states = get_branch_states(left_start)
    right_states = get_branch_states(right_start)
    
    # Get all transitions for each branch
    left_trans = [t for t in auto.transitions if t.from_state in left_states]
    right_trans = [t for t in auto.transitions if t.from_state in right_states]
    
    # Product state map
    state_map = {}
    
    def get_product_state(l_state, r_state):
        if (l_state, r_state) not in state_map:
            if l_state == left_start and r_state == right_start:
                state_map[(l_state, r_state)] = current
            else:
                state_map[(l_state, r_state)] = auto.new_state()
        return state_map[(l_state, r_state)]
    
    final = get_product_state(left_end, right_end)
    
    # Build synchronous product with self-loop allowance
    worklist = [(left_start, right_start)]
    visited = set()
    
    while worklist:
        l_state, r_state = worklist.pop(0)
        if (l_state, r_state) in visited:
            continue
        visited.add((l_state, r_state))
        
        product_state = get_product_state(l_state, r_state)
        
        # Get transitions from current states
        left_trans_here = [t for t in left_trans if t.from_state == l_state]
        right_trans_here = [t for t in right_trans if t.from_state == r_state]
        
        # Synchronous step: pick one from left AND one from right, merge labels
        for left_t in left_trans_here:
            for right_t in right_trans_here:
                # Merge labels from both transitions
                merged_labels = left_t.label | right_t.label
                
                # Next product state
                next_product = get_product_state(left_t.to_state, right_t.to_state)
                
                # Add merged transition
                auto.add_transition(product_state, next_product, merged_labels,
                                  is_blocking=left_t.is_blocking or right_t.is_blocking,
                                  is_epsilon=left_t.is_epsilon and right_t.is_epsilon,
                                  is_internal_choice=left_t.is_internal_choice or right_t.is_internal_choice,
                                  is_exclusive_choice=left_t.is_exclusive_choice or right_t.is_exclusive_choice,
                                  is_offering_choice=left_t.is_offering_choice or right_t.is_offering_choice,
                                  is_conditional_epsilon=left_t.is_conditional_epsilon and right_t.is_conditional_epsilon)
                
                if (left_t.to_state, right_t.to_state) not in visited:
                    worklist.append((left_t.to_state, right_t.to_state))
        
        # Self-loops can happen independently (for blocking)
        for left_t in left_trans_here:
            # Self-loop on left side
            if left_t.from_state == left_t.to_state:
                next_product = get_product_state(left_t.to_state, r_state)
                auto.add_transition(product_state, next_product, left_t.label,
                                  is_blocking=left_t.is_blocking,
                                  is_epsilon=left_t.is_epsilon,
                                  is_internal_choice=left_t.is_internal_choice,
                                  is_exclusive_choice=left_t.is_exclusive_choice,
                                  is_offering_choice=left_t.is_offering_choice,
                                  is_conditional_epsilon=left_t.is_conditional_epsilon)
                if (left_t.to_state, r_state) not in visited:
                    worklist.append((left_t.to_state, r_state))
        
        for right_t in right_trans_here:
            # Self-loop on right side
            if right_t.from_state == right_t.to_state:
                next_product = get_product_state(l_state, right_t.to_state)
                auto.add_transition(product_state, next_product, right_t.label,
                                  is_blocking=right_t.is_blocking,
                                  is_epsilon=right_t.is_epsilon,
                                  is_internal_choice=right_t.is_internal_choice,
                                  is_exclusive_choice=right_t.is_exclusive_choice,
                                  is_offering_choice=right_t.is_offering_choice,
                                  is_conditional_epsilon=right_t.is_conditional_epsilon)
                if (l_state, right_t.to_state) not in visited:
                    worklist.append((l_state, right_t.to_state))
        
        # If one side has finished, allow the other side to complete independently
        # (for non-self-loop transitions only)
        if r_state == right_end:
            # Right has finished, left can still take non-self-loop transitions
            for left_t in left_trans_here:
                if left_t.from_state != left_t.to_state:  # Not a self-loop
                    next_product = get_product_state(left_t.to_state, r_state)
                    auto.add_transition(product_state, next_product, left_t.label,
                                      is_blocking=left_t.is_blocking,
                                      is_epsilon=left_t.is_epsilon,
                                      is_internal_choice=left_t.is_internal_choice,
                                      is_exclusive_choice=left_t.is_exclusive_choice,
                                      is_offering_choice=left_t.is_offering_choice,
                                      is_conditional_epsilon=left_t.is_conditional_epsilon)
                    if (left_t.to_state, r_state) not in visited:
                        worklist.append((left_t.to_state, r_state))
        
        if l_state == left_end:
            # Left has finished, right can still take non-self-loop transitions
            for right_t in right_trans_here:
                if right_t.from_state != right_t.to_state:  # Not a self-loop
                    next_product = get_product_state(l_state, right_t.to_state)
                    auto.add_transition(product_state, next_product, right_t.label,
                                      is_blocking=right_t.is_blocking,
                                      is_epsilon=right_t.is_epsilon,
                                      is_internal_choice=right_t.is_internal_choice,
                                      is_exclusive_choice=right_t.is_exclusive_choice,
                                      is_offering_choice=right_t.is_offering_choice,
                                      is_conditional_epsilon=right_t.is_conditional_epsilon)
                    if (l_state, right_t.to_state) not in visited:
                        worklist.append((l_state, right_t.to_state))
    
    # Delete original branch transitions
    for trans in left_trans + right_trans:
        if trans in auto.transitions:
            auto.transitions.remove(trans)
    
    # Delete original branch states except current
    states_to_delete = (left_states | right_states) - {current}
    for state_id in states_to_delete:
        if state_id in auto.states:
            del auto.states[state_id]
    
    return final
    


def build_automaton(session_type: SessionType) -> Automaton:
    auto = Automaton()
    initial = auto.new_state()
    auto.initial = initial



    def build(st: SessionType, current: int) -> int:
        if st.kind == TypeKind.END:
            # End state is accepting
            auto.states[current].accepting = True
            auto.add_transition(current, current, {'#end'}, is_epsilon=False)
            return current
        
        if st.kind == TypeKind.ACTION or st.kind == TypeKind.BLOCKING_ACTION:
            next_s = auto.new_state()
            is_external_recursive = [(t.to_state, t.label) for t in auto.transitions if t.from_state == current and all(l.startswith('#ac') for l in t.label)]
            is_blocking = st.kind == TypeKind.BLOCKING_ACTION
            is_future = any('#F' in label.label for label in auto.transitions 
                          if label.from_state == current and label.to_state == current)
            if is_blocking:
                if is_future:
                    auto.add_transition(current, current, {'#F_' + st.label.replace('_', '')}, is_epsilon=False)
                    auto.delete_transition(current, current, '#F')
                    label = {'#FB_' + st.label[2:]}
                else:
                    auto.add_transition(current, current, {'#_' + st.label.replace('_', '')}, is_epsilon=False)
                    label = {st.label}
            else:
                if is_future:
                    label = {'#F_' + st.label}
                else:
                    label = {st.label}
            auto.add_transition(current, next_s, label, is_conditional_epsilon=True)
            for (to_state, ac_label) in is_external_recursive:
                auto.add_transition(next_s, to_state, ac_label, is_epsilon=False)
            return next_s
        
        if st.kind == TypeKind.DELAY:
            # Delay (#) - represents a synchronous instant/clock tick
            is_external_recursive = [(t.to_state, t.label) for t in auto.transitions if t.from_state == current and all(l.startswith('#ac') for l in t.label)]
            next_s = auto.new_state()
            for (to_state, ac_label) in is_external_recursive:
                auto.add_transition(next_s, to_state, ac_label, is_epsilon=False)
            auto.add_transition(current, next_s, {'#'}, is_epsilon=False)
            return next_s
        
        if st.kind == TypeKind.FUTURE:
            auto.add_transition(current, current, {'#F'}, is_epsilon=True)
            # Or start the actual behavior
            return build(st.first, current)

        if st.kind == TypeKind.SEQUENCE:
            mid = build(st.first, current)
            auto.states[mid].accepting = False
            return build(st.second, mid)
        
        if st.kind == TypeKind.PARALLEL:
            # s1 || s2: Both must happen, in any interleaving
            # Build each branch from a SEPARATE initial state, then merge
            
            # Create separate starting states for each branch
            left_start = auto.new_state()
            right_start = auto.new_state()
            
            # Build branches from their own starting states
            left_end = build(st.first, left_start)
            right_end = build(st.second, right_start)
            
            # Create asynchronous product - merge branches into interleaving
            final = create_async_product_branches(auto, left_end, right_end, current, left_start, right_start)
            
            return final
        
        if st.kind == TypeKind.INTERNAL_CHOICE:
            # s1 + s2: Process chooses non-deterministically
            # Build as parallel-style product: both branches in sequence with sync token
            # m1+m2 becomes: m1; #c; m2 (both must be taken, choice token ensures sync)
            
            if len(st.options) == 2:
                # Create separate start states for each branch
                left_start = auto.new_state()
                right_start = auto.new_state()
                
                # Build both branches
                left_end = build(st.options[0], left_start)
                right_end = build(st.options[1], right_start)
                
                # Use parallel-style product to merge branches with choice sync
                final = create_choice_product_branches(auto, left_end, right_end, current, 
                                                      left_start, right_start, is_internal=True)
                return final
            else:
                # For more than 2 options: build sequentially with #c between each
                # m1+m2+m3 becomes m1; #c; m2; #c; m3
                current_state = current
                for i, opt in enumerate(st.options):
                    opt_end = build(opt, current_state)
                    
                    if i < len(st.options) - 1:
                        # Not the last option, add #c transition
                        next_state = auto.new_state()
                        auto.add_transition(opt_end, next_state, {'#c'}, is_epsilon=False)
                        current_state = next_state
                    else:
                        # Last option
                        current_state = opt_end
                
                return current_state
        
        if st.kind == TypeKind.EXTERNAL_CHOICE:
            # a1:s1 & a2:s2: Offering choice - branches can loop back OR converge
            # All branches lead back to current (for repetition) AND to common final (for continuation)
            final = auto.new_state()

            all_blocking = True
            all_non_blocking = True
            collective_labels_str = ''
            for labels,_ in st.branches:
                if not labels.startswith('B_'):
                    all_blocking = False
                else:
                    all_non_blocking = False
                collective_labels_str += '::' + labels.replace('_', '')
            
            if all_blocking:
                auto.add_transition(current, current, {'#EC' + collective_labels_str}, is_epsilon=False)
            elif not all_non_blocking:
                raise ValueError("Mixed blocking and non-blocking labels in external choice branches.")
            
            for label, cont in st.branches:
                branch_s = auto.new_state()
                is_blocking = label.startswith('B_') if label else False
                auto.add_transition(current, branch_s, {label}, is_blocking=is_blocking, 
                                  is_offering_choice=True)
                branch_end = build(cont, branch_s)
                # Add #ac transition from branch end back to current (for looping/repetition)
                auto.states[branch_end].accepting = False
                # remove end transition if any
                auto.delete_transition(branch_end, branch_end, '#end')
                auto.add_transition(branch_end, current, {'#ac' + collective_labels_str}, is_epsilon=False)
                # Also add epsilon transition to final (for continuation/exit)
                auto.add_transition(branch_end, final, {' ε '}, is_epsilon=True)
                auto.add_transition(final, current, {'#ac' + collective_labels_str}, is_epsilon=False)
            
            return final
        
        if st.kind == TypeKind.EXCLUSIVE_CHOICE:
            # a1:s1 ^ a2:s2: Exclusive choice (pick exactly one)
            end = auto.new_state()
            for label, cont in st.branches:
                branch_s = auto.new_state()
                is_blocking = label[0].startswith('B_') if label else False
                auto.add_transition(current, branch_s, {label}, is_blocking=is_blocking,
                                  is_exclusive_choice=True)
                branch_end = build(cont, branch_s)
                if branch_end != end:
                    auto.add_transition(branch_end, end, {'e'}, is_epsilon=True)
                    auto.states[branch_end].accepting = False
            
            return end
        
        return current
    
    final_state = build(session_type, initial)
    auto.states[final_state].accepting = True
    auto.add_transition(final_state, final_state, {'#end'}, is_epsilon=False)
    return auto

def print_debug(auto: Automaton):
    print("States:")
    for sid, state in auto.states.items():
        acc = " (accepting)" if state.accepting else ""
        print(f"  State {sid}{acc}")
    print("Transitions:")
    for trans in auto.transitions:
        labels_str = ', '.join(sorted(trans.label))
        print(f"  {trans.from_state} --{{{labels_str}}}--> {trans.to_state}")
    print()




def print_automaton(auto: Automaton, id):
    with open(f"scratch/automaton_{id}.dot", "w") as f:
        f.write("digraph G {\n")
        for sid, state in auto.states.items():
            shape = "doublecircle" if state.accepting else "circle"
            f.write(f'  {sid} [shape={shape}];\n')
        for trans in auto.transitions:
            labels_str = ', '.join(sorted(trans.label))
            f.write(f'  {trans.from_state} -> {trans.to_state} [label="{labels_str}"];\n')
        f.write("}")
    os.system(f"dot -Tpng scratch/automaton_{id}.dot -o scratch/automaton_{id}.png")
    if debug_mode:
        print(f"Automaton {id} graph saved to scratch/automaton_{id}.png")

def check_compatibility(auto1: Automaton, auto2: Automaton, verbose=False) -> Tuple[bool, str]:
    _, compatible, reason = create_product_automaton(auto1, auto2)
    if not compatible:
        return False, reason
    return True, "No deadlocks detected; types are compatible."

def main():
    print("=" * 60)
    print("Session Type Compatibility Checker (-d for debug mode)")
    print("=" * 60)
    print("\nSyntax:")
    print("  m1;m2     - Sequence")
    print("  m1||m2    - Parallel")
    print("  m1+m2     - Internal choice")
    print("  m1&m2     - Offering choice")
    print("  m1^m2     - Exclusive choice")
    print("  F m1      - Future (eventual)")
    print("  B_m1      - Blocking action")
    print("  end       - End state")
    print("=" * 60)

    if len(sys.argv) > 1 and sys.argv[1] == '-d':
        global debug_mode
        debug_mode = True

    while True:
        print("\n")
        type1_str = input("Type 1 (or 'quit'): ").strip()
        if type1_str.lower() == 'quit':
            break
        
        type2_str = input("Type 2: ").strip()
        
        try:
            parser1 = Parser(type1_str)
            type1 = parser1.parse()
            
            parser2 = Parser(type2_str)
            type2 = parser2.parse()
            
            auto1 = build_automaton(type1)
            auto2 = build_automaton(type2)
            auto3, compatible , reason = create_product_automaton(auto1, auto2)

            if (debug_mode):
                os.system("rm -rf scratch")
                os.makedirs("scratch", exist_ok=True)
                print_automaton(auto1, 1)
                print_automaton(auto2, 2)

                img1 = Image.open(os.path.join(PWD, "scratch", "automaton_1.png"))
                img2 = Image.open(os.path.join(PWD, "scratch", "automaton_2.png"))

                if auto3 != None:
                    print_automaton(auto3, 3)
                    img3 = Image.open(os.path.join(PWD, "scratch", "automaton_3.png"))
                    total_width = img1.width + img2.width + img3.width
                    max_height = max(img1.height, img2.height, img3.height)
                    new_img = Image.new('RGB', (total_width, max_height))
                    new_img.paste(img1, (0,0))
                    new_img.paste(img2, (img1.width,0))
                    new_img.paste(img3, (img1.width + img2.width, 0))
                else:
                    total_width = img1.width + img2.width
                    max_height = max(img1.height, img2.height)
                    new_img = Image.new('RGB', (total_width, max_height))
                    new_img.paste(img1, (0,0))
                    new_img.paste(img2, (img1.width,0))

                new_img.show()
            print("-" * 60)            
            if compatible:
                print("COMPATIBLE")
            else:
                print("INCOMPATIBLE")
            print(reason)
            print("-" * 60)
        except Exception as e:
            print(f"\nError: {e}")
            traceback.print_exc()

if __name__ == "__main__":
    main()