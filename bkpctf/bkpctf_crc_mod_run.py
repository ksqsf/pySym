#!/usr/bin/env python
from copy import copy
import z3
import pySym

proj = pySym.Project("./bkpctf_crc_mod.py")

def hook_crc(state):
    shift = int(state.getVar('shift'))
    mesg = state.getVar('mesg')
    CRC_POLY = state.getVar('CRC_POLY', ctx=0)
    Then = []
    Else = []
    If = copy(mesg[shift]).getZ3Object() != 0

    print("Hit hook. Shift == " + str(shift))

    for i in range(65):
        old_c = copy(mesg[shift+i])
        new_c = mesg[shift+i]
        new_c.increment()
        Then.append(new_c.getZ3Object() == old_c.getZ3Object() ^ CRC_POLY[i].getZ3Object())
        Else.append(new_c.getZ3Object() == old_c.getZ3Object())

    state.addConstraint(z3.If(If, z3.And(Then), z3.And(Else)))

proj.hook(21, hook_crc)
pg = proj.factory.path_group(ignore_groups='deadended')

pg.explore()
