# Sistema Deduttivo per la Logica Modale S4.2 in Agda

## Descrizione del progetto
Questo progetto nasce come parte di uno stage universitario e ha come obiettivo l’**implementazione, nel proof assistant [Agda](https://agda.readthedocs.io/)**, di un **sistema deduttivo in deduzione naturale per la logica modale S4.2**.

L’attività si colloca nell’ambito della **logica matematica** e dell’**informatica teorica**, con un approccio formale alla rappresentazione e verifica di sistemi logici tramite tipi dipendenti.

Il progetto adotta la metodologia del **deep embedding**, ovvero la rappresentazione di un sistema logico all’interno di un altro (Agda) tramite **tipi induttivi**, al fine di studiarne la **metateoria** e dimostrarne proprietà fondamentali come la **normalizzazione**.

---

## Obiettivi
1. Studiare la letteratura scientifica relativa alle **logiche modali**, con particolare attenzione al sistema **S4.2**.
2. Acquisire familiarità con il **proof assistant Agda** e con i concetti base dei **tipi dipendenti**.
3. Implementare in Agda:
   - la **sintassi** del linguaggio della logica modale S4.2;
   - le **regole deduttive** del sistema in deduzione naturale.
4. Esplorare la possibilità di formalizzare e dimostrare il **teorema di normalizzazione**, risultato centrale nella teoria della dimostrazione.

---

## Contesto teorico
La logica modale S4.2 è un’estensione della logica modale S4 che aggiunge assiomi per modellare nozioni di **necessità** e **possibilità** in contesti più ricchi, come quelli epistemici o topologici.

Nel formalismo della **deduzione naturale**, le regole inferenziali sono espresse in termini di introduzione ed eliminazione dei connettivi, e in questo progetto tali regole saranno **codificate in Agda** tramite **tipi induttivi**.

---

## Requisiti
- **Agda** ≥ 2.6.4  
  → [Installazione ufficiale](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
- **Agda Standard Library** (consigliata)
  ```bash
  agda --version
  agda -i . -i /path/to/stdlib
  ```

