# A library of non-degenerate edge-transitive maps

* version 0.1
* Author: Alen Orbanic

- copy the folder to the magma's working directory.
- In Magma type: 
  load "etran/etran.m";

- ... it will take some time to load ...


Usage: open file etran.m and check functions' comments.

Some examples:
- get the first map in table in Phd (Alen Orbanic: Edge-transitive maps) 
at the beginning of the table "Type 2P - non-orientable genus 3-30" on the page  70.

> mp1 := getMap(2, "PD", "2");

- get also the second end the third map from the same table:

> mp2 := getMap(1, "PD", "2");
> mp3 := getMap(19, "PD", "2");

The first argument in 'getMap' is 'id', the second can be one of "", "D", "P", "PD" and the third 
can be one of "1", "2", "2ex", "3", "4", "5".

To obtain map info:

> getMapInfo(mp1);

For other interesting functions/operations on maps check function comments in etran/etran.m


