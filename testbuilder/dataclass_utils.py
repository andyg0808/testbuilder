from typing import Any, Type

import dataclasses


def make_extended_instance(instance: Any, new_type: Type, **args: Any) -> Any:
    fields = {}
    for f in dataclasses.fields(instance):
        if f.name not in args:
            data = getattr(instance, f.name)
            fields[f.name] = data
    return new_type(**args, **fields)
