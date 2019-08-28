from enum import IntEnum

class ThreeValuedBool(IntEnum):
    TRUE = 2
    MAYBE = 1
    FALSE = 0

    def _not(self):

        if self == TRUE:
            return FALSE
        elif self == FALSE:
            return TRUE
        else:
            return MAYBE

    def _and(self, other):
        if self == FALSE or other == FALSE:
            return FALSE
        elif self == MAYBE or other == MAYBE:
            return MAYBE
        else:
            return TRUE

    def _or(self, other):
        if self == TRUE or other == TRUE:
            return TRUE
        elif self == MAYBE or other == MAYBE:
            return MAYBE
        else:
            return FALSE

    def __str__(self):
        if self == TRUE:
            return 'TRUE'
        elif self == MAYBE:
            return 'MAYBE'
        else:
            return 'FALSE'


TRUE = ThreeValuedBool.TRUE
FALSE = ThreeValuedBool.FALSE
MAYBE = ThreeValuedBool.MAYBE