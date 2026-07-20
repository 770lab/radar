# 📡 Radar

**https://770lab.com/radar/** — la carte de ceux qui sont là, en direct.

Chaque visiteur qui accepte la géolocalisation apparaît sur la carte de tous
les autres, tant que sa page reste ouverte. Tu fermes → tu disparais.
Rien n'est enregistré.

## Fonctionnement

- **Front** : statique (GitHub Pages), vanilla JS + [Leaflet](https://leafletjs.com)
  (tuiles CARTO dark), tout vendorisé dans `vendor/`.
- **Temps réel** : Firebase Realtime Database (`radar-770lab`, europe-west1),
  auth anonyme.
- **Présence** : `/presence/$uid` avec `onDisconnect().remove()` (disparition
  auto à la fermeture), heartbeat 25 s, blip grisé après 75 s sans signe de vie,
  nettoyage des nœuds zombie après 10 min (autorisé par les règles).

## Sécurité / vie privée

- Lecture publique de `/presence` (c'est le principe du site), écriture
  uniquement sur son propre nœud (auth anonyme), schéma strictement validé
  par `database.rules.json`.
- Position partagée uniquement après opt-in explicite, arrondie à ~10 cm
  (6 décimales), jamais persistée côté serveur au-delà de la session.
- Pseudos échappés avant insertion dans le DOM (pas de XSS via la DB).

## Développement

```bash
python3 -m http.server 8123   # puis http://localhost:8123
```

Déployer les règles RTDB après modification :

```bash
firebase deploy --only database --project radar-770lab
```

Le site se déploie tout seul : push sur `main` → GitHub Pages.
