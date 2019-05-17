#!/bin/sh
cd $(dirname "$0")
for FILE in collision_safe.asd mesh_lt.asd mesh_gt.asd ball_table_image.asd
do
  marshall $FILE > $FILE.out
  diff $FILE.out $FILE.out.expected
done
diff ball_table.bmp ball_table.bmp.expected