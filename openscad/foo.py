#!/user/bin/env python3
from solid import *
from solid.objects import union
from solid.utils import *
import pdb
from math import sin
import numpy as np

SEGMENTS = 48

origin = np.array([0,0,0])
eigen_x = np.array([1,0,0])
eigen_y = np.array([0,1,0])
eigen_z = np.array([0,0,1])

class Axle():
    def __init__(self, r=None, h=None, c=None):
        self.r = r or 0.25
        self.h = h or 5
        self.c = Blue
    @bom_part("Axle", 100, currency="USD", link="http://example.io/M3x16", leftover=0)
    def value(self, explode_t=None):
        return color(self.c)(cylinder(r=self.r, h=self.h))


class Wheel():
    def __init__(self, axle, r=None, h=None, c=None):
        self.axle = axle
        self.r = r or 2 
        self.h = h or .5
        self.c = Red
    @bom_part("Wheel", 50, currency="USD", link="http://example.io/M3x16", leftover=0)
    def value(self, explode_t=None):
        return color(self.c)(cylinder(r=self.r, h=self.h)) - hole()(self.axle.value(explode_t=explode_t))

class WheelSet():
    def __init__(self, a=None, lw=None, rw=None):
        self.a = a or Axle()
        self.lw = lw or Wheel(self.a)
        self.rw = rw or Wheel(self.a)
    def value(self, explode_t=None):
        magnitude = explode_t or 0
        sm = sin(magnitude) * 3
        assembly = translate(-1*sm*eigen_z)(self.lw.value(explode_t=explode_t)) \
                + self.a.value(explode_t=explode_t) \
                + translate(1*sm*eigen_z)(up(self.a.h - self.rw.h)(self.rw.value(explode_t=explode_t)))
        return translate((0, -self.a.h/2, 0))(rotate([0,90,90])(assembly))

class Suspension():
    def __init__(self, l=None, h = None, w = None):
        self.l = l or 10
        self.h = h or .25 * self.l
        self.w = w or .25 * self.l
    @bom_part("Suspension", 100, currency="USD", link="http://example.io/M3x16", leftover=0)
    def value(self, explode_t=None):
        return translate((-self.l / 2, -self.w / 2, -self.h / 2)) \
                    (cube((self.l, self.w, self.h)))

class Carriage():
    def __init__(self, fw=None, rw=None, s=None):
        self.fw = fw or WheelSet()
        self.rw = rw or WheelSet()
        self.s = s or Suspension()
    def value(self, explode_t=None):
        magnitude = explode_t or 0
        sm = sin(magnitude) * 2
        front_axle_offset = (
                -self.s.l / 2 + self.fw.a.r * 2, 
                0, 
                0)
        rear_axle_offset = (
                self.s.l / 2 - self.rw.a.r * 2, 
                0,
                0)
        return translate(sm*eigen_z)(self.s.value(explode_t)) \
                + translate(sm*eigen_x)(translate(front_axle_offset)(self.fw.value(explode_t))) \
                + translate(-1*sm*eigen_x)(translate(rear_axle_offset)(self.rw.value(explode_t)))
        

class ExplodingCarriage():
    def __init__(self, c):
        self.c = c
    def value(self):
        """Return animate function"""
        def my_animate(_time: Optional[float] = 0) -> OpenSCADObject:
            return self.c.value(explode_t=_time)
        return my_animate

if __name__ == '__main__':
    #scad_render_to_file(WheelSet().value(), file_header=f'$fn = {SEGMENTS};', include_orig_code=False)
    #scad_render_to_file(Suspension().value(), file_header=f'$fn = {SEGMENTS};', include_orig_code=False)
    #scad_render_to_file(Carriage().value(), file_header=f'$fn = {SEGMENTS};', include_orig_code=False)

    file_out = scad_render_animated_file(ExplodingCarriage(Carriage()).value(),  # A function that takes a float argument
                                         # called '_time' in [0,1)
                                         # and returns an OpenSCAD object
                                         steps=20,  # Number of steps to create one complete motion
                                         back_and_forth=True,  # If true, runs the complete motion
                                         # forward and then in reverse,
                                         # to avoid discontinuity
                                         out_dir=".",
                                         include_orig_code=False,  # Append SolidPython code
                                         file_header=f'$fn = {SEGMENTS};'
                                         )
    print(f"{__file__}: SCAD file written to: \n{file_out}")
    bom = bill_of_materials(csv=True)
    print(bom)
