import collections
import copy
import logging

LOG = logging.getLogger(__name__)


class AbstractState:
    TRANSFORMERS = collections.defaultdict(dict)

    @classmethod
    def transforms(cls, stmt_type):
        def decorator(func):
            cls.TRANSFORMERS[cls][stmt_type] = func
            return func
        return decorator

    def copy(self):
        return copy.deepcopy(self)

    def transform(self, statement):
        LOG.debug('Processing statement %s', statement)
        res = self.copy()
        # LOG.debug('Initial state is: %s\n', res)
        try:
            transformer = self.TRANSFORMERS[type(self)][type(statement)]
        except KeyError:
            LOG.warning(f'No transformer for {statement}')
            return res

        transformer(res, statement)
        res.post_transform()
        # LOG.debug('Transformed state is: %s\n', res)
        return res

    # Augment / Coerce
    def post_transform(self):
        pass
