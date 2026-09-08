"""Process-level trusted-network prohibition.

This is defense in depth, not an OS sandbox.  Canonical release evidence must
also be produced by an executor whose egress is disabled outside the process.
"""
from __future__ import annotations

from contextlib import contextmanager
import socket
from typing import Iterator

from .errors import CalculatorError


@contextmanager
def trusted_offline() -> Iterator[None]:
    original_socket = socket.socket
    original_create_connection = socket.create_connection

    class OfflineSocket(original_socket):
        def connect(self, address):  # type: ignore[override]
            raise CalculatorError("TRUSTED_NETWORK_ACCESS_FORBIDDEN", detail=str(address))

        def connect_ex(self, address):  # type: ignore[override]
            raise CalculatorError("TRUSTED_NETWORK_ACCESS_FORBIDDEN", detail=str(address))

    def forbidden(*args, **kwargs):
        raise CalculatorError("TRUSTED_NETWORK_ACCESS_FORBIDDEN")

    socket.socket = OfflineSocket
    socket.create_connection = forbidden
    try:
        yield
    finally:
        socket.socket = original_socket
        socket.create_connection = original_create_connection
