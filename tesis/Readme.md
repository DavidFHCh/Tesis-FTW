Makefile para un proyecto en Coq:
- crear un archivo titulado "\_CoqProject" con la siguiente linea y los archivos con su extension .v

   -R . MiProyecto

  el proyecto tendra por titulo MiProyecto
- para crear el makefile, desde una terminal ingresar la siguiente linea

  coq_makefile -f \_CoqProyect -o Makefile

- el archivo se creara con el nombre Makefile y
  para iniciar coqide con las rutas correctas para las dependencias
  se debe ejecutar mediante:

  coqide -R . MiProyecto miarchivo.v

-----------------------------------
De los archivos de Graciela Lopez Campos

Los preliminares son:
AB.hs --> Sec 1.3   y   
ABB.has --> Sec 1.4

Los archivos a traducir a Coq son:
+ ARNo.hs --> Sec 2.1
+ ARNci1.hs --> Sec 3.1
+ ARNci2.hs --> Sec 3.2 -> no se puede porque la clase de EQ no esta traducida
+ ARNac.hs --> Sec 3.3 -> trabo mi computadora, aparte el insert no pasaba y lo tuve que borrar.
+ ARTa_V2_set.hs --> Sec 3.4








[david@Stardust hs-to-coq]$ stack exec hs-to-coq -- -o ../output/ ../implementacionesV2/ARNTA_v2_set.hs

../implementacionesV2/ARNTA_v2_set.hs:148:22: error:
    • Illegal instance declaration for ‘Del t’
        (All instance types must be of the form (T a1 ... an)
         where a1 ... an are *distinct type variables*,
         and each type variable appears at most once in the instance head.
         Use FlexibleInstances if you want to disable this.)
    • In the instance declaration for ‘Del t’
    |
148 | instance Delred t => Del t where
    |                      ^^^^^

../implementacionesV2/ARNTA_v2_set.hs:219:10: error:
    • Illegal instance declaration for ‘Set (RBT EmptyT)’
        (All instance types must be of the form (T a1 ... an)
         where a1 ... an are *distinct type variables*,
         and each type variable appears at most once in the instance head.
         Use FlexibleInstances if you want to disable this.)
    • In the instance declaration for ‘Set (RBT EmptyT)’
    |
219 | instance Set (RBT EmptyT) where
    |          ^^^^^^^^^^^^^^^^

+ ARNta.hs --> Sec 3.4
mismo error de arriba, relacionado con FlexibleInstances.


Leyendo acerca de las FlexibleInstances, los foros y lugares de haskell dicen porque es bueno usarlas, pero no que son.

Con Gilborto tenemos la sospecha de que de alguna manera le dicen a Haskell que no sea tan estricto con su chequeo de tipos, lo cual me causa ruido con el hecho de la traduccion a Coq.


--------------------------------------------------------------------------------

Si se quieren checar los archivos que se han generado hasta el momento se hace lo siguiente:

+ Se copia de la carpeta lastAdvances/ cualquiera de los archivos ahi encontrados a la carpeta hs-to-coq/bases
+ Se abre con Coqide y se pueden ver los archivos.



Hasta ahorita el archivo mas cercano al exito es la insercion, hay dos casos que probablemte no se puedan solucionar.

La eliminacion esta en sus primeras etapas ya que el script todavia no se logra que se ejecute correctamente.


La herramienta hs-to-coq ha probado se util pero no tanto como se pensaba en un inicio, al ser una herramienta en desarrollo,
esta no genera codigo 100% proof ready, se tienen que hacer ajustes al codigo, ya que suele traducir a cosas que todavia no tiene 
implentadas por parte de la biblioteca estandar de haskell.


-------------------------------------------------------------------------------

Se agrega la primera parte de la documentacion del archivo de insercion de arboles rojinegros.

Se puede generar con make install-doc desde el directorio hs-to-coq/base.
