from typing import Any, Type, TypeVar

import dataclasses

T = TypeVar("T")


def make_extended_instance(instance: Any, new_type: Type[T], **args: Any) -> T:
    fields = {}
    for f in dataclasses.fields(instance):
        if f.name not in args:
            data = getattr(instance, f.name)
            fields[f.name] = data
    return new_type(**args, **fields)  # type: ignore
