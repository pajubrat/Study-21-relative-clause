
# template3_2.py
# Python script for paper Brattico, P. (2026). Finnish relative clause and the derivational search function.

import sys
import copy
import itertools
major_lexical_categories = ['C', 'N', 'v', 'V', 'T/inf', 'A', 'D', 'Dem','Adv', 'T', 'P', 'a', 'b', 'c', 'd']

log_file = open('log.txt', 'w', encoding='utf-8')


# Auxiliary functions used during certain processing steps
def sWMcopy(sWM, SO):
    """
    This function copies syntactic objects in sWM and SO
    and updates internal links (adjuncts, chains, copy-links)
    """
    sWM2 = [x.copy() for x in sWM if x not in set(SO)]
    SO2 = [x.copy() for x in SO]
    # Updates internal links
    for x in sWM2 + SO2:
        update_links(x)
    return set(sWM2), tuple(SO2)

def update_links(X):
    """
    Updates internal links inside syntactic object X
    """
    if X.adjunct:
        X.mother = X.mother.isomapping
    if X.adjuncts:
        X.adjuncts = {x.isomapping for x in X.adjuncts if x}
    if X.copied:
        X.copied = X.copied.isomapping
    if not X.zero_level():
        update_links(X.left())
        update_links(X.right())


def tset(X):
    if isinstance(X, set):
        return X
    else:
        return {X}


def print_lst(lst):
    return ', '.join([f'{x}' for x in lst])


def print_constituent_lst(sWM):
    str = f'{print_ordered_lst([x for x in sWM if not x.adjunct])}'
    if [x for x in sWM if x.adjunct]:
        str += f' | {print_adjunct_lst([x for x in sWM if x.adjunct])}'
    return str


def print_adjunct_lst(lst):
    return ', '.join(sorted([f'{x}(:{x.mother.head().lexical_category()})' for x in lst], key=str.casefold, reverse=True))


def print_ordered_lst(lst):
    return ', '.join(sorted([f'{x}' for x in lst], key=str.casefold, reverse=True))


class SpeakerLexicon:
    """Stores the lexical knowledge for a group of people, i.e. a language, dialect, register"""
    def __init__(self, L, ld):
        self.speaker_lexicon = dict()          # Speaker lexicon, as dictionary
        self.create_speaker_lexicon(L, ld)     # Create speaker lexicon
        self.apply_redundancy_rules(ld)

    def create_speaker_lexicon(self, L, ld):
        """Creates a speaker lexicon by applying redundancy rules"""
        for lex in ld.root_lexicon.keys():
            features = set(ld.root_lexicon[lex])
            if self.target_language(features, L):
                self.speaker_lexicon[lex] = features
                self.speaker_lexicon[lex].add(L)

    def target_language(self, features, L):
        """
        Determines whether lexical features 'features' belong to lexical item in language 'language'.
        It does if there is no contradictory language feature; feature sets with no language specification
        are assumed to be universal and belong to all languages
        """
        for f in features:
            if f.startswith('LANG:') and f != L:
                return False
        return True

    def apply_redundancy_rules(self, ld):
        """Composes the speaker lexicon from the list of words and lexical redundancy rules"""
        for trigger_features_str in ld.root_lexical_redundancy_rules.keys():
            trigger_features = set(trigger_features_str.strip().split(' '))
            for lex in self.speaker_lexicon.keys():
                if trigger_features <= self.speaker_lexicon[lex] and '-LRR' not in self.speaker_lexicon[lex]:
                    self.speaker_lexicon[lex] = self.speaker_lexicon[lex] | ld.root_lexical_redundancy_rules[trigger_features_str]

    def retrieve(self, name):
        """Retrieves lexical items from the speaker lexicon and wraps them
        into zero-level phrase structure objects"""
        X0 = PhraseStructure()
        X0.features = self.speaker_lexicon[name]
        X0.phonological_exponent = self.get_phonology(name)
        if X0.phonological_exponent == '0':     # Phonologically null elements are not visible in the output
            X0.elliptic = True
        X0.zero = True
        return X0

    def get_phonology(self, name):
        return next((x[5:] for x in self.speaker_lexicon[name] if x.startswith('PHON:')), name)

    def __str__(self):
        stri = ''
        for lex in self.speaker_lexicon.keys():
            stri += f'{lex} = {" ".join([f for f in sorted(list(self.speaker_lexicon[lex]))])}; '
        return stri

class PhraseStructure:
    """Simple asymmetric binary-branching bare phrase structure formalism"""
    logging = None              # class variable: whether logging is on or off, affects calculation speed
    chain_index = 1             # class variable: creates chain indexes
    logging_report = ''         # class variable: used to store logging information during the derivation
    logging_report_detailed = ''

    def __init__(self, X=None, Y=None):
        self.const = (X, Y)             # Constituents are represented as tuples
                                        # Alternatives: list; axiomatic left/right constituents; dictionary
        self.features = set()           # Features (set of string literals)
        self.mother = None              # Phrase structure geometry...
        if X:                           # ...
            X.mother = self             # ...
        if Y:                           # ...
            Y.mother = self             # ...
        self.zero = False               # Whether the object is a zero-level object
        self.elliptic = False           # Ellipsis due to copying
        self.copied = None              # Copy link

        # Auxiliary properties not part of the empirical theory
        self.adjuncts = set()           # Stores the set of adjuncts adjoined to the constituent
                                        # This is an auxiliary structure that is not part of the theory and simplifies
                                        # certain calculations
        self.adjunct = False            # Auxiliary assumption, not part of theory
        self.isomapping = None         # Auxiliary structure for backtracking purposes
        self.chain_index = 0            # Initial chain index
        self.phonological_exponent = '' # Phonological exponent of the constituent, used in printout and linearization

    def left(X):
        """Abstraction for the notion of left daughter"""
        return X.const[0]

    def right(X):
        """Abstraction for the notion of right daughter"""
        return X.const[1]

    def Merge(X, Y):
        """Standard Merge"""
        return PhraseStructure(X, Y)

    def isLeft(X):
        """Determines whether X is the left constituent"""
        return X.sister() and X.mother.left() == X

    def isRight(X):
        """Determines whether X is the right constituent"""
        return X.sister() and X.mother.right() == X

    def phrasal(X):
        """Defines the notion of phrasal constituent"""
        return X.left() and X.right()

    def scan_features(X, fset):
        return fset <= X.features or (X.phrasal() and (X.left().scan_features(fset) or X.right().scan_features(fset)))

    def is_adjunct(X):
        """X is an adjunct iff X has mother Y but is not constituent of Y"""
        return X.mother and X not in X.mother.const

    def copy(X):
        """Recursive copying for constituents"""
        if not X.terminal():
            Y = PhraseStructure(X.left().copy(), X.right().copy())
        else:
            Y = PhraseStructure()
        return Y.copy_properties(X)

    def copy_properties(Y, X):
        """Copies properties of X into Y and returns Y."""
        Y.phonological_exponent = X.phonological_exponent
        Y.features = X.features
        Y.zero = X.zero
        Y.copied = X.copied
        Y.chain_index = X.chain_index
        Y.elliptic = X.elliptic
        Y.adjuncts = X.adjuncts
        Y.adjunct = X.adjunct
        if X.adjunct:
            Y.mother = X.mother
        X.isomapping = Y
        return Y

    def chaincopy(X):
        """Grammatical copying operation, with phonological silencing"""
        if not X.zero_level():  # Head movement does not create chain indexes
            X.label_chain()     # Create chain information, not part of the theory
        Y = X.copy()        # Copying
        X.elliptic = True   # Mark the source elliptic
        Y.copied = X        # Marking the copy chain
        return Y

    def zero_level(X):
        """Zero-level categories are considered primitive by phrasal syntactic rules"""
        return X.zero or X.terminal()

    def terminal(X):
        """Terminal elements do not have constituents"""
        return not X.right() and not X.left()

    def MergeComposite(X, Y):
        """
        Composite Merge operation contains head and phrasal movements (if applicable) and Merge.
        This format was adopted in the main article, but is not the only model possible. An alternative is
        to detach head movement and phrasal movement into their own operations that are applied independently
        by the derivational search function
        """
        return X.HeadMovement(Y).Merge(Y).PhrasalMovement()

    def MergePreconditions(X, Y):
        """
        Preconditions for Merge. These conditions apply at each merge operation and
        restrict the derivational search space.
        """
        if X.isRoot() and Y.isRoot():                                   # Both elements must be roots (no mother)
            if Y.terminal() and Y.obligatory_wcomplement_features():    # Y cannot be merged if it can only be a
                                                                        # word-internal constituent. Empirical assumption
                                                                        # that plays no role in the discussion in the
                return False                                            # main article.
            if X.zero_level():                                          # If X is zero-level, then Y must satisfy its
                return X.complement_subcategorization(Y)                # subcategorization features under [X Y(P)]
            if Y.zero_level():                                          # If Y is zero-level, then
                return Y.complement_subcategorization(None) and Y.head().specifier_subcategorization(X)
            return Y.head().specifier_subcategorization(X)

    def HeadMovement(X, Y):
        """Implementation for head movement"""
        if X.HeadMovementPreconditions(Y):
            PhraseStructure.logging_report += f'\n\t+ Head chain by {X}° targeting {Y.head()}°'
            return Y.head().chaincopy().HeadMerge_(X)   # Under [X YP], pick the head Y, copy it and merge with X.
        return X    # If the preconditions are not satisfied, return an unmodified X

    def HeadMovementPreconditions(X, Y):
        """
        Head movement preconditions which apply during each Merge operation [X YP]:
        (i) X must be zero-level, phrasal constituents cannot trigger it;
        (ii) X must be bound morpheme, don't combine free morphemes;
        (iii) X cannot create complex heads directly without head movement (if they can, then that option must be used)
        """
        return X.zero_level() and \
               X.bound_morpheme() and \
               not X.mandateDirectHeadMerge()

    def PhrasalMovement(X):
        """Implementation for phrasal movement: first A-bar movement, then A-movement"""
        return X.phrasal_A_bar_movement().phrasal_A_movement()

    def phrasal_A_bar_movement(X):
        """
        Implementation for phrasal A-bar movement for phrase X. The conditions are:
        (i) The head of X is a scope-marking element (e.g. C; X = CP);
        (ii) the head of X is an operator (e.g., C[wh]);
        (iii) the complement of X contains an item with [wh];
        (iv) the item marked with [wh] has not already been moved;
        """
        if X.head().scope_marker() and \
                X.head().operator() and \
                X.head().complement() and \
                X.head().complement().internal_search('OP') and \
                not X.head().complement().internal_search('OP').elliptic:
            PhraseStructure.logging_report += f'\n\t+ Phrasal A-bar chain by {X.head()}° targeting {X.head().complement().internal_search("OP")}'
            return X.head().complement().internal_search('OP').chaincopy().Merge(X)
        return X

    def operator_variable_condition(X):
        """This function simulates operator-variable interpretations"""
        if X.zero_level():
            if X.operator() and X.scope_marker() and not X.scan_features({'AUX'}):
                if not X.complement() or not X.complement().internal_search('OP'):
                    PhraseStructure.logging_report_detailed += f'\n\t*Operator {X} without variable.'
                    return False
            return True
        else:
            if X.head().operator() and not X.head().scope_marker():
                if not X.copied and not X.elliptic and '-INSITU' in X.head().features:
                    PhraseStructure.logging_report_detailed += f'\n\t*Operator {X} in situ.\n'
                    return False
            return X.left().operator_variable_condition() and X.right().operator_variable_condition()

    def phrasal_A_movement(X):
        """
        Implementation for phrasal A-movement. The operation applies iff
        (i) the head of X has the EPP-feature;
        (ii-iii) the head of X has a phrasal complement YP;
        (iv) YP contains a suitable element that can be moved.
        """
        if X.head().EPP() and X.head().complement() and X.head().complement().phrasal() and X.head().complement().A_goal():
            PhraseStructure.logging_report += f'\n\t+ Phrasal A chain by {X.head()}° targeting {X.head().complement().A_goal()}'
            return X.head().complement().A_goal().chaincopy().Merge(X)
        return X

    def A_goal(X):
        return X.internal_search('D')

    def HeadMerge_(X, Y):
        """Direct Head Merge creates zero-level objects from two zero-level objects"""
        Z = X.Merge(Y)
        Z.zero = True
        Z.features = Y.features     #   Feature inheritance
        Z.adjuncts = Y.adjuncts     #   Feature inheritance
        return Z

    def HeadMergePreconditions(X, Y):
        """Preconditions for direct Head Merge are that both objects must be
        zero-level objects, Y must select X and license the operation"""
        return X.zero_level() and \
               Y.zero_level() and \
               Y.w_selects(X) and \
               Y.mandateDirectHeadMerge()

    def w_selects(Y, X):
        """Word-internal selection (X Y) where Y w-selects X"""
        return Y.leftmost().obligatory_wcomplement_features() <= X.rightmost().features

    def leftmost(X):
        while X.left():
            X = X.left()
        return X

    def rightmost(X):
        while X.right():
            X = X.right()
        return X

    def Adjoin_(X, Y):
        """Adjunction creates asymmetric constituents with mother-of dependency without
        daughter dependency"""
        X.mother = Y
        X.adjunct = True
        Y.adjuncts.add(X)   # This is not part of theory, not realistic component, but simplifies printout
        return {X, Y}

    def AdjunctionPreconditions(X, Y):
        return X.isRoot() and \
               Y.isRoot() and \
               X.head().license_adjunction() and \
               X.head().license_adjunction() in Y.head().features

    def label_chain(X):
        if X.chain_index == 0:
            PhraseStructure.chain_index += 1
            X.chain_index = PhraseStructure.chain_index

    def external_search(X, fset):
        Origin = X
        while X:
            if X != Origin:
                for x in (X,) + X.const:
                    if x and x != Origin and fset <= x.features:
                        return x
            X = X.mother

    def internal_search(X, f):
        while X:
            for c in X.const:
                if c and f in c.head().features:
                    return c
            X = X.right()

    def head(X):
        return next((x for x in (X,) + X.const if x and x.zero_level()), X.phrasal() and X.right().head())

    def sister(X):
        if X.mother:
            return next((const for const in X.mother.const if const != X), None)

    def complement(X):
        if X.zero_level() and X.isLeft():
            return X.sister()

    def subcategorization(X):
        """
        Recursive interface test for complement and specifier subcategorization; an example
        of how to test subcategorization as an output well-formedness condition.
        """
        if X.zero_level():
            return X.complement_subcategorization(X.complement()) and \
                   X.specifier_subcategorization() and \
                   X.w_subcategorization()
        return X.left().subcategorization() and X.right().subcategorization()

    def w_subcategorization(X):
        """Word-internal subcategorization which applies when heads are merged directly
        to create zero-level constituents."""
        if X.terminal():
            if X.obligatory_wcomplement_features() and 'PC:_X_' not in X.features:
                PhraseStructure.logging_report_detailed += f'\n\t*|{X}| is a bound morpheme'
                return False
        if X.left() and X.right():
            if not X.right().w_selects(X.left()):
                PhraseStructure.logging_report_detailed += f'\n\t*w-selection violation by |{X}|°'
                return False
        if X.left() and not X.left().terminal():
            if not X.left().w_subcategorization():
                PhraseStructure.logging_report_detailed += f'\n\t*w-selection violation by |{X}|°'
                return False
        if X.right() and not X.right().terminal():
            if not X.right().w_subcategorization():
                PhraseStructure.logging_report_detailed += f'\n\t*w-selection violation by |{X}|°'
                return False
        return True

    def complement_subcategorization(X, Y):
        """Complement subcategorization under [X Y]"""
        if (not Y and (not X.selected_features('COMP:') or 'ø' in X.selected_features('COMP:'))) or \
                (Y and X.selected_features('COMP:') and
                 Y.head().check(X.selected_features('COMP:')) and
                 Y.head().subcategorization()):
            return True
        PhraseStructure.logging_report_detailed += f'\n\t*Complement selection violation by |{X}|° ({X.get_selection_features()})'

    def specifier_subcategorization(X, Spec=None):
        """Specifier subcategorization under [XP YP]"""
        if not Spec:
            if not X.specifier():
                if X.selected_features('SPEC:') and 'ø' not in X.selected_features('SPEC:'):
                    PhraseStructure.logging_report_detailed += f'\n\t*Missing specifier selection violation by |{X}|° ({X.get_selection_features()})'
                    return False
                return True
            Spec = X.specifier()

        # Deletes multiple specifier constructions (ad hoc rule). The real principle has to do with
        # thematic roles: formal specifier positions are unable to assign thematic roles (semantics)
        if Spec and Spec.mother and Spec.mother.sister() and not Spec.mother.sister().zero_level():
            PhraseStructure.logging_report_detailed += f'\n\t*Multiple  specifier selection violation by |{X}|° ({X.get_selection_features()})'
            return False

        if not X.selected_features('SPEC:') or not Spec.head().check(X.selected_features('SPEC:')):
            PhraseStructure.logging_report_detailed += f'\n\t*Positive specifier selection violation by |{X}|° ({X.get_selection_features()}) against {Spec}'
            return False
        return True

    def check(X, features):
        return {f for f in features if f != 'ø'} & X.features

    def phi_check(X):
        """Verifies that there are no phi-feature mismatches (concord, agreement)"""

        # π triggers agreement requirement
        if X.zero_level():
            if 'π' in X.features:
                Y = X.external_search({'D'})
                if Y:
                    if not X.Agree(Y, 'PHI:'):
                        PhraseStructure.logging_report_detailed += f'\n\t*Agreement error between |{X}| and |{Y}|'
                        return False
            return True
        else:
            return X.left().phi_check() and X.right().phi_check()

    def Agree(X, Y, fclass):
        """Verifies that X and Y do not contain type-value mismatches in class [fclass]"""
        return next((False for pair in itertools.product({f for f in X.features if f.startswith(fclass)}, {f for f in Y.features if f.startswith(fclass)}) if pair[0].split(':')[1] == pair[1].split(':')[1] and pair[0].split(':')[2] != pair[1].split(':')[2]), True)

    def case_checking(X):
        # Only base-positions are checked for case configurations
        if X.copied:
            return True
        # Recursion
        if not X.zero_level():
            return X.left().case_checking() and X.right().case_checking()
        # Either (i) X is not case assignee or it is and
        # (ii) we have unmarked (NOM) option or
        # (iii) there is a suitable case assigner (κ-head)
        if not X.case_assignee_features() or \
                (not X.external_search({'κ'}) and 'ø' in X.case_assignee_features()) or \
                (X.external_search({'κ'}) and X.external_search({'κ'}).features & X.case_assignee_features()):
            return True
        # ... otherwise checking fails.
        PhraseStructure.logging_report_detailed += f'\n\t*|{X}| failed case checking for {X.case_assignee_features()}'

    def case_assignee_features(X):
        for f in X.features:
            if ':' in f and f.split(':')[0] == 'κ':
                return set(f.split(':')[1].split(','))

    def selected_features(X, type):
        s = set()
        for f in X.features:
            if f.startswith(type):
                s = s | set(f.split(':')[1].split(','))
        return s

    def specifier(X):
        """
        Specifier of X is phrasal left constituent inside the project from X. The definition of
        specifier is controversial. This returns the left phrasal constituent closest to the head (of) X.
        """
        x = X.head()
        while x and x.mother and x.mother.head() == X:
            if x.mother.left() != X:
                return x.mother.left()
            x = x.mother

    def linearize(X):
        """Linearization algorithm that is unrealistic but written to be as easy as possible
        to understand"""
        stri = ''
        # Linearize left adjuncts first
        stri += ''.join([x.linearize() for x in X.adjuncts if x and x.linearizes_left()])
        # Linearize X if it is not elliptic
        if not X.elliptic:
            if X.zero_level():
                # Word-internal linearization by different function, which is realistic
                stri += X.linearize_word()[:-1] + ' '
            else:
                stri += ''.join([x.linearize() for x in X.const])
        # Linearize right adjuncts last
        stri += ''.join([x.linearize() for x in X.adjuncts if x and x.linearizes_right()])
        return stri

    def linearize_word(X):
        """Spellout algorithm for words, creates morpheme boundaries marked by symbol #
        This function would include all word-internal e.g. morphophonological operations that
        apply inside words.
        """
        if X.terminal():
            return X.phonological_exponent + '#'
        return ''.join([x.linearize_word() for x in X.const])

    def bound_morpheme(X):
        """Definition for bound morpheme"""
        return 'PC:#X' in X.features and 'PC:_X_' not in X.features

    def auxiliary(X):
        return 'AUX' in X.features

    def EPP(X):
        """Definition for EPP"""
        return 'EPP' in X.features

    def operator(X):
        """Definition for operators"""
        return 'OP' in X.features

    def scope_marker(X):
        """Definition for scope markers"""
        return 'SCOPE' in X.features

    def linearizes_left(X):
        """Adjunct linearization to left is controlled by a lexical feature"""
        return 'λ:L' in X.head().features

    def linearizes_right(X):
        """Adjunct linearization to right is controlled by a lexical feature"""
        return 'λ:R' in X.head().features

    def get_selection_features(X):
        return ' '.join([x for x in X.features if x.startswith('COMP:') or x.startswith('SPEC:')])

    def isRoot(X):
        """Roots are constituents that do not have mothers"""
        return not X.mother

    def mandateDirectHeadMerge(X):
        return 'ε' in X.features

    def obligatory_wcomplement_features(X):
        return {f.split(':')[1] for f in X.features if f.startswith('+wCOMP')}

    def license_adjunction(X):
        return next((f.split(':')[1] for f in X.features if f.startswith('α:')), None)

    def __str__(X):
        """Simple printout function for phrase structure objects"""
        if X.elliptic and not X.zero:
            return '__' + X.get_chain_subscript()
        if X.terminal():
            return X.phonological_exponent
        elif X.zero_level():
            return '(' + ' '.join([f'{x}' for x in X.const]) + ')'
        return f'[{X.head().lexical_category()}P ' + ' '.join([f'{x}' for x in X.const]) + ']' + X.get_chain_subscript()

    def get_chain_subscript(X):
        if X.chain_index != 0:
            return ':' + str(X.chain_index)
        return ''

    def lexical_category(X):
        """# Defines the major lexical categories used in all printouts"""
        return next((f for f in major_lexical_categories if f in X.features), '?')

class LogicalForm():
    def __init__(self):
        pass

    def interface_check(self, X):
        return X.subcategorization() and \
               X.operator_variable_condition() and \
               X.case_checking() and X.phi_check()

class SpeakerModel():
    """Models a group of speakers (e.g., language, dialect, age)"""
    def __init__(self, ld, language):
        # List of all syntactic operations available in the grammar
        self.syntactic_operations = [(PhraseStructure.MergePreconditions, PhraseStructure.MergeComposite, 2, 'Merge'),
                                     (PhraseStructure.HeadMergePreconditions, PhraseStructure.HeadMerge_, 2, 'Head Merge'),
                                     (PhraseStructure.AdjunctionPreconditions, PhraseStructure.Adjoin_, 2, 'Adjoin')]
        self.n_accepted = 0                             # Number of accepted sentences
        self.n_steps = 0                                # Number of steps consumed
        self.output_data = set()                        # A set containing all output data
        self.lexicon = SpeakerLexicon(language, ld)     # Speaker lexicon
        self.LF = LogicalForm()                         # Syntax-semantics interface
        self.language = language

    def derive(self, numeration):
        """Finds all derivations from numeration"""
        self.n_steps = 0
        self.output_data = set()
        self.n_accepted = 0
        self.derivational_search_function([self.lexicon.retrieve(item) for item in numeration])

    def derivational_search_function(self, sWM):
        """Derivational search function"""
        if self.derivation_is_complete(sWM):
            self.process_final_output(sWM)
        else:
            for Preconditions, OP, n, name in self.syntactic_operations:
                for SO in itertools.permutations(sWM, n):
                    if Preconditions(*SO):
                        PhraseStructure.logging_report += f'\t{name.upper()}({print_lst(SO)})'
                        sWM_, SO_ = sWMcopy(sWM, SO)
                        new_sWM = sWM_ | tset(OP(*SO_))
                        self.consume_resource(new_sWM, sWM)
                        self.derivational_search_function(new_sWM)
            log_file.write('.')

    def __str__(self):
        return f'\nSpeaker Model {self.language}:\n{self.lexicon}\n'

    @staticmethod
    def derivation_is_complete(sWM):
        return len({X for X in sWM if X.isRoot()}) == 1

    @staticmethod
    def root_structure(sWM):
        return next((X for X in sWM if not X.mother))

    def consume_resource(self, new_sWM, old_sWM):
        """
        Resource recording, this is what gets printed into the log file.
        Modify to enhance readability and to reflect the operations available in the grammar
        """
        self.n_steps += 1
        log_file.write(f'\n\n{self.n_steps}.\t{{ {print_constituent_lst(old_sWM)} }}\n')
        log_file.write(f'{PhraseStructure.logging_report} =')
        log_file.write(f'\n\t{{ {print_constituent_lst(new_sWM)} }}')
        PhraseStructure.logging_report = ''
        PhraseStructure.logging_report_detailed = ''

    def process_final_output(self, sWM):
        PhraseStructure.chain_index = 0
        PhraseStructure.logging_report_detailed = ''
        for X in sWM:
            if not self.LF.interface_check(X):
                log_file.write(f'{PhraseStructure.logging_report_detailed}')
                return
        self.n_accepted += 1
        prefix = f'{self.n_accepted}'
        output_sentence = f'{self.root_structure(sWM).linearize()}'
        print(f'\n({prefix}.)\n{output_sentence}\n{print_constituent_lst(sWM)}\n')   # Print the output
        log_file.write(f'\n=>\t/{output_sentence[:-1]}/ accepted.')
        self.output_data.add(output_sentence.strip())
        log_file.write('\n')


class LanguageData:
    """Stores and manipulates all data used in the simulation, including logging output"""
    def __init__(self, filename):
        self.study_dataset = []     # dataset is a list of (numeration, set of target sentences) tuples
        self.root_lexicon = dict()                       # Root lexicon contains the whole lexicon from the file
        self.root_lexical_redundancy_rules = dict()      # Root redundancy rules
        self.read_root_lexicon(filename)        # Read the root lexicon
        self.languages = self.set_languages()

    def read_root_lexicon(self, filename):
        """Reads the root lexicon (all lexical items and redundancy rules)"""
        with open(filename, encoding='utf-8') as f:
            for line in f.readlines():
                line = line.strip()
                if not line.startswith('#'):
                    if '::' in line:
                        key, features_str = line.split('::')
                        features = set(features_str.strip().split(' '))
                        self.root_lexicon[key.strip()] = features
                    if '=>' in line:
                        trigger, features = line.split('=>')
                        self.root_lexical_redundancy_rules[trigger.strip()] = set(features.strip().split(' '))

    def set_languages(self):
        Ls = set()
        for key in self.root_lexicon:
            for f in self.root_lexicon[key]:
                if f.startswith('LANG:'):
                    Ls.add(f)
        return Ls

    def guess_language(self, numeration):
        for x in numeration:
            if x in self.root_lexicon.keys():
                for f in self.root_lexicon[x]:
                    if f.startswith('LANG:'):
                        return f

    # Read the dataset
    def read_dataset(self, filename):
        numeration = []
        dataset = set()
        with open(filename) as f:
            lines = f.readlines()
            for line in lines:
                line = line.strip()
                if line.strip() and not line.startswith('#') and not line.startswith("\'") and not line.startswith('END'):
                    line = line.strip()
                    if line.startswith('Numeration='):
                        if numeration:
                            self.study_dataset.append((numeration, dataset))
                            dataset = set()
                        # Items in the numeration are separated by comma
                        numeration = [word.strip() for word in line.split('=')[1].split(',')]
                    else:
                        dataset.add(line.strip())
                if line.startswith('END'):
                    break
            self.study_dataset.append((numeration, dataset))

    def print_root_lexicon(self):
        stri = 'ROOT LEXICON:\n'
        for key in self.root_lexicon.keys():
            stri += f'{key}: {self.root_lexicon[key]}\n'
        return stri + '\n\n'

    def evaluate_experiment(self, output_from_simulation, gold_standard_dataset, n_steps):
        print(f'\tDerivational steps: {n_steps}')
        overgeneralization = output_from_simulation - gold_standard_dataset
        undergeneralization = gold_standard_dataset - output_from_simulation
        errors = len(overgeneralization) + len(undergeneralization)
        print(f'\tErrors {errors}')
        if errors > 0:
            print(f'\tShould not generate: {overgeneralization}')
            print(f'\tShould generate: {undergeneralization}')
            sys.exit()
        return errors

# Run one whole study as defined by the dataset file, itself containing
# numeration-target sentences blocks
def run_study(ld, speaker_models):
    n_dataset = 0           #   Number of datasets in the experiment (counter)
    n_total_errors = 0      #   Count the number of errors in the whole experiment (counter)
    n_total_steps = 0       #   Number of calculations steps in the whole experiment
    for numeration, gold_standard_dataset in ld.study_dataset:
        n_dataset += 1
        L = ld.guess_language(numeration)
        print(f'Dataset {n_dataset} ({numeration}, {L}):')
        log_file.write('\n---------------------------------------------------\n')
        log_file.write(f'Dataset {n_dataset}:\n')
        log_file.write(f'Numeration: {numeration}, {L}\n')
        log_file.write(f'Predicted outcome: {gold_standard_dataset}')

        speaker_models[L].derive(numeration)

        n_total_errors += ld.evaluate_experiment(speaker_models[L].output_data, gold_standard_dataset, speaker_models[L].n_steps)
        n_total_steps += speaker_models[L].n_steps
    print(f'\nTotal errors {n_total_errors} after {n_total_steps} calculation steps.\n')
    log_file.write(f'\nTotal errors: {n_total_errors}')

ld = LanguageData('lexicon.txt')             #   Instantiate language data object, including root lexicons
ld.read_dataset('dataset.txt')      #   Name of the dataset file processed by the script, reads the file
speaker_models = {}
log_file.write(f'Root lexicon: {ld.root_lexicon}\n')

# Create speaker models for languages present in the lexicon
for L in ld.languages:
    speaker_models[L] = SpeakerModel(ld, language=L)
    log_file.write(f'Speaker Model {L} lexicon: {speaker_models[L].lexicon}\n')

run_study(ld, speaker_models)
