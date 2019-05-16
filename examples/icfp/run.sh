#!/bin/sh
date
for FILE in cam_piston.asd mesh_lt.asd mesh_gt.asd plot2.asd
do
  /usr/bin/time -l marshall $FILE > $FILE.expected_out
  date
done
